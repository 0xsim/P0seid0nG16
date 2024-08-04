use bellman::{
    gadgets::{
        num::AllocatedNum,
    },
    groth16, Circuit, ConstraintSystem, SynthesisError,
};
use bls12_381::{Bls12, Scalar};
use ff::Field;
use rand::rngs::OsRng;

const T: usize = 3; // Number of elements in the state
const FULL_ROUNDS: usize = 4; // Simplified: 4 full rounds
const PARTIAL_ROUNDS: usize = 4; // Simplified: 4 partial rounds

// Struct to represent our circuit
#[derive(Clone)]
struct PoseidonCircuit {
    input: Option<Scalar>,
}

impl Circuit<Scalar> for PoseidonCircuit {
    fn synthesize<CS: ConstraintSystem<Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        // Allocate the input as a private input
        let input = AllocatedNum::alloc(cs.namespace(|| "input"), || {
            self.input.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Initialize state
        let mut state = vec![input];
        for i in 1..T {
            state.push(AllocatedNum::alloc(cs.namespace(|| format!("state_{}", i)), || {
                Ok(Scalar::zero())
            })?);
        }

        // Simplified round constants and MDS matrix
        let round_constant = Scalar::from(5u64); // Simplified: use a constant value
        let mds_matrix = vec![Scalar::from(2u64); T]; // Simplified: use a constant matrix

        // Perform Poseidon permutation
        for r in 0..FULL_ROUNDS + PARTIAL_ROUNDS {
            // Add round constants
            for i in 0..T {
                let tmp = AllocatedNum::alloc(cs.namespace(|| format!("tmp_{}_{}", r, i)), || {
                    Ok(state[i].get_value().unwrap() + round_constant)
                })?;
                cs.enforce(
                    || format!("add_constant_{}_{}", r, i),
                    |lc| lc + state[i].get_variable() + (round_constant, CS::one()),
                    |lc| lc + CS::one(),
                    |lc| lc + tmp.get_variable(),
                );
                state[i] = tmp;
            }

            // Apply S-box (x^5)
            if r < FULL_ROUNDS / 2 || r >= FULL_ROUNDS / 2 + PARTIAL_ROUNDS {
                // Full round
                for i in 0..T {
                    let squared = state[i].square(cs.namespace(|| format!("squared_{}_{}", r, i)))?;
                    let fourth = squared.square(cs.namespace(|| format!("fourth_{}_{}", r, i)))?;
                    let fifth = AllocatedNum::alloc(cs.namespace(|| format!("fifth_{}_{}", r, i)), || {
                        Ok(state[i].get_value().unwrap() * fourth.get_value().unwrap())
                    })?;
                    cs.enforce(
                        || format!("constrain_fifth_{}_{}", r, i),
                        |lc| lc + state[i].get_variable(),
                        |lc| lc + fourth.get_variable(),
                        |lc| lc + fifth.get_variable(),
                    );
                    state[i] = fifth;
                }
            } else {
                // Partial round
                let squared = state[0].square(cs.namespace(|| format!("squared_{}", r)))?;
                let fourth = squared.square(cs.namespace(|| format!("fourth_{}", r)))?;
                let fifth = AllocatedNum::alloc(cs.namespace(|| format!("fifth_{}", r)), || {
                    Ok(state[0].get_value().unwrap() * fourth.get_value().unwrap())
                })?;
                cs.enforce(
                    || format!("constrain_fifth_{}", r),
                    |lc| lc + state[0].get_variable(),
                    |lc| lc + fourth.get_variable(),
                    |lc| lc + fifth.get_variable(),
                );
                state[0] = fifth;
            }

            // Mix
            let old_state = state.clone();
            for i in 0..T {
                let mut acc = AllocatedNum::alloc(cs.namespace(|| format!("mix_acc_init_{}_{}", r, i)), || {
                    Ok(Scalar::zero())
                })?;
                for j in 0..T {
                    let product = AllocatedNum::alloc(cs.namespace(|| format!("product_{}_{}", r, i)), || {
                        Ok(old_state[j].get_value().unwrap() * mds_matrix[j])
                    })?;
                    cs.enforce(
                        || format!("mix_mul_{}_{}", r, i),
                        |lc| lc + old_state[j].get_variable(),
                        |lc| lc + (mds_matrix[j], CS::one()),
                        |lc| lc + product.get_variable(),
                    );
                    let new_acc = AllocatedNum::alloc(cs.namespace(|| format!("new_acc_{}_{}", r, i)), || {
                        Ok(acc.get_value().unwrap() + product.get_value().unwrap())
                    })?;
                    cs.enforce(
                        || format!("mix_add_{}_{}", r, i),
                        |lc| lc + acc.get_variable() + product.get_variable(),
                        |lc| lc + CS::one(),
                        |lc| lc + new_acc.get_variable(),
                    );
                    acc = new_acc;
                }
                state[i] = acc;
            }
        }

        // Expose the first element of the state as the hash result
        state[0].inputize(cs.namespace(|| "expose result"))?;

        Ok(())
    }
}

// Function to create and verify a Groth16 proof
fn create_and_verify_proof() -> Result<(), SynthesisError> {
    // Create a random input
    let input = Scalar::random(&mut OsRng);
    println!("Input: {:?}", input);

    // Create an instance of our circuit
    let circuit = PoseidonCircuit {
        input: Some(input),
    };

    // Generate the Groth16 parameters
    println!("Generating Groth16 parameters...");
    let params = groth16::generate_random_parameters::<Bls12, _, _>(circuit.clone(), &mut OsRng)?;

    // Create a Groth16 proof
    println!("Creating Groth16 proof...");
    let proof = groth16::create_random_proof(circuit, &params, &mut OsRng)?;

    // Prepare the verification key
    let pvk = groth16::prepare_verifying_key(&params.vk);

    // Compute the expected result (simplified Poseidon hash)
    let mut state = vec![input, Scalar::zero(), Scalar::zero()];
    let round_constant = Scalar::from(5u64);
    let mds_matrix = vec![Scalar::from(2u64); T];

    for r in 0..FULL_ROUNDS + PARTIAL_ROUNDS {
        // Add round constants
        for i in 0..T {
            state[i] += round_constant;
        }

        // Apply S-box
        if r < FULL_ROUNDS / 2 || r >= FULL_ROUNDS / 2 + PARTIAL_ROUNDS {
            for i in 0..T {
                state[i] = state[i].pow(&[5, 0, 0, 0]);
            }
        } else {
            state[0] = state[0].pow(&[5, 0, 0, 0]);
        }

        // Mix
        let old_state = state.clone();
        for i in 0..T {
            state[i] = Scalar::zero();
            for j in 0..T {
                state[i] += old_state[j] * mds_matrix[j];
            }
        }
    }

    let expected_result = state[0];
    println!("Expected result: {:?}", expected_result);

    // Verify the proof
    println!("Verifying proof...");
    let result = groth16::verify_proof(&pvk, &proof, &[expected_result]);
    match result {
        Ok(_) => println!("Proof verification result: Valid"),
        Err(e) => println!("Proof verification error: {:?}", e),
    }

    Ok(())
}

fn main() {
    match create_and_verify_proof() {
        Ok(_) => println!("Proof creation and verification completed."),
        Err(e) => println!("An error occurred: {:?}", e),
    }
}