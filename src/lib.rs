extern crate ethereum_types;
extern crate keccak_hash;

use ethereum_types::H256;
use keccak_hash::keccak;
use std::collections::HashMap;
use std::vec::Vec;

pub type Bytes = std::vec::Vec<u8>;

pub struct SparseMerkleTree {
    /// the ith element holds all non-default nodes in the tree with height i.
    nodes: Vec<HashMap<u64, H256>>,
    /// number of edges from root to leaf, where a leaf is either the hash of
    /// a LeafItem or H(0).
    depth: usize,
    /// a hash for each level of the tree, where all leaves = H(0).
    default_hashes: Vec<H256>,
}

impl SparseMerkleTree {
    pub fn new(leaf_items: Vec<impl LeafItem>) -> Self {
        let mut leaves = HashMap::new();
        for item in leaf_items {
            leaves.insert(item.slot(), item.hash());
        }
        SmtBuilder::tree(leaves)
    }

    pub fn proof(&self, leaf_item: impl LeafItem) -> SmtProof {
        SmtProver::proof(leaf_item.slot(), &self.nodes)
    }

    /// Returns true if the given leaf item is part of this merkle tree,
    /// using proof to reconstruct the root.
    pub fn verify(&self, leaf_item: impl LeafItem, proof: SmtProof) -> bool {
        let proof_root =
            SmtProver::proof_root(leaf_item.slot(), &self.nodes, &self.default_hashes, proof);
        proof_root == self.root()
    }

    pub fn root(&self) -> H256 {
        match self.nodes[self.depth].get(&0) {
            Some(root) => root.clone(),
            None => self.default_hashes[self.depth].clone(),
        }
    }
}

/// LeafItem is a type from which a SparseMerkleTree can be constructed out
/// of, e.g., a set of Transactions for a plasma block.
pub trait LeafItem {
    fn slot(&self) -> u64;
    fn hash(&self) -> H256;
}

struct SmtBuilder;
impl SmtBuilder {
    fn tree(leaves: HashMap<u64, H256>) -> SparseMerkleTree {
        let depth = 64;
        let default_hashes = Self::default_hashes(depth);

        let mut nodes = vec![leaves.clone()];
        let mut curr_nodes = leaves;
        for curr_level in 0..depth {
            let mut parent_nodes = HashMap::new();
            for (slot, node) in curr_nodes.iter() {
                let parent = Self::parent_node(slot, node, &curr_nodes, default_hashes[curr_level]);
                if let Some(parent_hash) = parent {
                    parent_nodes.insert(slot / 2, parent_hash);
                }
            }
            nodes.push(parent_nodes.clone());
            curr_nodes = parent_nodes;
        }

        SparseMerkleTree {
            nodes,
            depth,
            default_hashes,
        }
    }

    /// Returns a vector of hashes of length height, were
    /// hash[i] = keccak(hash[i-1], hash[i-1]).
    fn default_hashes(depth: usize) -> Vec<H256> {
        let mut hashes = vec![keccak(H256::from(0))];
        for k in 1..depth + 1 {
            let mut input = vec![];
            let last = hashes[k - 1];
            input.extend(&last[..]);
            input.extend(&last[..]);
            hashes.push(keccak(input));
        }
        hashes
    }

    /// Returns the parent node of the given node in the merkle tree.
    /// Slot is the position of the given node at it's level (i.e. is it
    /// the first node, second node, etc).
    /// Level_nodes are all the nodes at the same level as the given node.
    /// Levl_default_hash is the default hash to use a this level.
    fn parent_node(
        slot: &u64,
        node: &H256,
        level_nodes: &HashMap<u64, H256>,
        level_default_hash: H256,
    ) -> Option<H256> {
        if slot % 2 == 0 {
            let sibling_slot = slot + 1;
            let parent_hash = match level_nodes.get(&sibling_slot) {
                Some(sibling_hash) => {
                    let mut input = vec![];
                    input.extend(&node[..]);
                    input.extend(&sibling_hash[..]);
                    keccak(input)
                }
                None => {
                    let mut input = vec![];
                    input.extend(&node[..]);
                    input.extend(&level_default_hash[..]);
                    keccak(input)
                }
            };
            Some(parent_hash)
        } else {
            let sibling_slot = slot - 1;
            if let None = level_nodes.get(&sibling_slot) {
                let mut input = vec![];
                input.extend(&level_default_hash[..]);
                input.extend(&node[..]);
                let parent_hash = keccak(input);
                Some(parent_hash)
            } else {
                // the left sibling is not default and so we'll calculate the
                // parent in the first case
                None
            }
        }
    }
}

struct SmtProver;
impl SmtProver {
    fn proof(slot: u64, nodes: &Vec<HashMap<u64, H256>>) -> SmtProof {
        let depth = 64;

        let mut is_default_bits = 0;
        let mut non_default_hashes = vec![];

        let mut slot = slot;

        for curr_level in 0..depth {
            let sibling_slot = if slot % 2 == 0 { slot + 1 } else { slot - 1 };
            if let Some(sibling) = nodes[curr_level].get(&sibling_slot) {
                non_default_hashes.extend(&sibling[..]);
                is_default_bits |= 1 << curr_level;
            }
            slot /= 2;
        }

        SmtProof {
            is_default_bits,
            non_default_hashes,
        }
    }

    fn proof_root(
        slot: u64,
        nodes: &Vec<HashMap<u64, H256>>,
        default_hashes: &Vec<H256>,
        proof: SmtProof,
    ) -> H256 {
        if nodes[0].get(&slot).is_none() {
            return H256::from(0);
        }

        let depth = 64;

        let mut proof_bits = proof.is_default_bits;
        let non_default_hashes = proof.non_default_hashes;
        let mut proof_index = 0;

        let mut curr_slot = slot;
        let mut root_builder = *nodes[0].get(&slot).unwrap();
        for curr_level in 0..depth {
            let sibling_hash = if proof_bits % 2 == 0 {
                &default_hashes[curr_level][..]
            } else {
                let non_default_sibling = &non_default_hashes[proof_index..proof_index + 32];
                proof_index += 32;
                non_default_sibling
            };
            // hash order changes if the curr node is a left or right child
            if curr_slot % 2 == 0 {
                let mut input = vec![];
                input.extend(&root_builder[..]);
                input.extend(&sibling_hash[..]);
                root_builder = keccak(input);
            } else {
                let mut input = vec![];
                input.extend(&sibling_hash[..]);
                input.extend(&root_builder[..]);
                root_builder = keccak(input);
            }

            proof_bits /= 2;
            curr_slot /= 2;
        }
        root_builder
    }
}

pub struct SmtProof {
    pub is_default_bits: u64,
    pub non_default_hashes: Bytes,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn loom_build_tests() {
        let cases = [
            (
                vec![],
                "6f35419d1da1260bc0f33d52e8f6d73fc5d672c0dca13bb960b4ae1adec17937",
            ),
            (
                vec![(
                    // slot
                    14414645988802088183 as u64,
                    // leaf_item hash
                    "4b114962ecf0d681fa416dc1a6f0255d52d701ab53433297e8962065c9d439bd",
                )],
                // expected merkle root
                "0ed6599c03641e5a20d9688f892278dbb48bbcf8b1ff2c9a0e2b7423af831a83",
            ),
            (
                vec![(
                    14414645988802088183 as u64,
                    "510a183d5457e0d22951440a273f0d8e28e01d15f750d79fd1b27442299f7220",
                )],
                "8d0ae4c94eaad54df5489e5f9d62eeb4bf06ff774a00b925e8a52776256e910f",
            ),
        ];

        for (leaves, expected_root) in cases.iter() {
            run_loom_test(leaves, expected_root);
        }
    }

    fn run_loom_test(leaves: &[(u64, &str)], expected_root: &str) {
        let tree = SmtBuilder::tree(build_leaves(leaves));

        let expected_root = H256::from_str(expected_root).unwrap();
        assert_eq!(tree.root(), expected_root);
    }

    fn build_leaves(leaves: &[(u64, &str)]) -> HashMap<u64, H256> {
        let mut leaf_hashes = HashMap::new();
        for (slot, leaf) in leaves {
            let leaf_hash = H256::from_str(leaf).unwrap();
            leaf_hashes.insert(*slot, leaf_hash);
        }
        leaf_hashes
    }

    #[test]
    fn loom_proof_tests() {
        let cases = [
            (
                // leaves to build tree with
                vec![(
                    14414645988802088183 as u64,
                    "510a183d5457e0d22951440a273f0d8e28e01d15f750d79fd1b27442299f7220",
                )],
                // slots to build proofs of and expected outcome
                vec![
                    (14414645988802088183 as u64, true),
                    (14414645988802088184 as u64, false),
                    (14414645988802088182 as u64, false),
                ],
            ),
            (
                vec![
                    (
                        2 as u64,
                        "cf04ea8bb4ff94066eb84dd932f9e66d1c9f40d84d5491f5a7735200de010d84",
                    ),
                    (
                        600 as u64,
                        "abcabcabacbc94566eb84dd932f9e66d1c9f40d84d5491f5a7735200de010d84",
                    ),
                    (
                        30000 as u64,
                        "abcaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1c9f40d84d5491f5a7735200de010d84",
                    ),
                ],
                vec![(2 as u64, true), (600 as u64, true), (30000 as u64, true)],
            ),
        ];
        for (leaves, slot_verifications) in cases.iter() {
            run_loom_proof_tests(leaves, slot_verifications);
        }
    }

    fn run_loom_proof_tests(leaves: &[(u64, &str)], slot_verifications: &[(u64, bool)]) {
        let tree = SmtBuilder::tree(build_leaves(&leaves));

        for (slot, expected_verification) in slot_verifications.iter() {
            let proof = SmtProver::proof(*slot, &tree.nodes);
            let result = SmtProver::proof_root(*slot, &tree.nodes, &tree.default_hashes, proof);
            if *expected_verification {
                assert_eq!(result, tree.root());
            } else {
                assert_eq!(result, H256::from(0));
            }
        }
    }
}
