module specs::validator_info_specs;

use ika_system::validator_info::{Self, ValidatorInfo};

use sui::vec_set::{Self, VecSet};
use std::string::String;
use sui::group_ops::Element;
use sui::table_vec::TableVec;
use sui::bls12381::UncompressedG1;

#[spec(prove, target = validator_info::validator_id, ignore_abort)]
fun validator_id_spec(self: &ValidatorInfo): ID {
    validator_info::validator_id(self)
}

#[spec(prove, target = validator_info::network_address, ignore_abort)]
fun network_address_spec(self: &ValidatorInfo): &String {
    validator_info::network_address(self)
}

#[spec(prove, target = validator_info::p2p_address, ignore_abort)]
fun p2p_address_spec(self: &ValidatorInfo): &String {
    validator_info::p2p_address(self)
}

#[spec(prove, target = validator_info::consensus_address, ignore_abort)]
fun consensus_address_spec(self: &ValidatorInfo): &String {
    validator_info::consensus_address(self)
}

#[spec(prove, target = validator_info::protocol_pubkey_bytes, ignore_abort)]
fun protocol_pubkey_bytes_spec(self: &ValidatorInfo): &vector<u8> {
    validator_info::protocol_pubkey_bytes(self)
}

#[spec(prove, target = validator_info::protocol_pubkey, ignore_abort)]
fun protocol_pubkey_spec(self: &ValidatorInfo): &Element<UncompressedG1> {
    validator_info::protocol_pubkey(self)
}

#[spec(prove, target = validator_info::network_pubkey_bytes, ignore_abort)]
fun network_pubkey_bytes_spec(self: &ValidatorInfo): &vector<u8> {
    validator_info::network_pubkey_bytes(self)
}

#[spec(prove, target = validator_info::consensus_pubkey_bytes, ignore_abort)]
fun consensus_pubkey_bytes_spec(self: &ValidatorInfo): &vector<u8> {
    validator_info::consensus_pubkey_bytes(self)
}

#[spec(prove, target = validator_info::mpc_data_bytes, ignore_abort)]
fun mpc_data_bytes_spec(self: &ValidatorInfo): &Option<TableVec<vector<u8>>> {
    validator_info::mpc_data_bytes(self)
}

#[spec(prove, target = validator_info::next_epoch_network_address, ignore_abort)]
fun next_epoch_network_address_spec(self: &ValidatorInfo): &Option<String> {
    validator_info::next_epoch_network_address(self)
}

#[spec(prove, target = validator_info::next_epoch_p2p_address, ignore_abort)]
fun next_epoch_p2p_address_spec(self: &ValidatorInfo): &Option<String> {
    validator_info::next_epoch_p2p_address(self)
}

#[spec(prove, target = validator_info::next_epoch_consensus_address, ignore_abort)]
fun next_epoch_consensus_address_spec(self: &ValidatorInfo): &Option<String> {
    validator_info::next_epoch_consensus_address(self)
}

#[spec(prove, target = validator_info::next_epoch_protocol_pubkey_bytes, ignore_abort)]
fun next_epoch_protocol_pubkey_bytes_spec(self: &ValidatorInfo): &Option<vector<u8>> {
    validator_info::next_epoch_protocol_pubkey_bytes(self)
}

#[spec(prove, target = validator_info::next_epoch_network_pubkey_bytes, ignore_abort)]
fun next_epoch_network_pubkey_bytes_spec(self: &ValidatorInfo): &Option<vector<u8>> {
    validator_info::next_epoch_network_pubkey_bytes(self)
}

#[spec(prove, target = validator_info::next_epoch_consensus_pubkey_bytes, ignore_abort)]
fun next_epoch_consensus_pubkey_bytes_spec(self: &ValidatorInfo): &Option<vector<u8>> {
    validator_info::next_epoch_consensus_pubkey_bytes(self)
}

#[spec(prove, target = validator_info::next_epoch_mpc_data_bytes, ignore_abort)]
fun next_epoch_mpc_data_bytes_spec(self: &ValidatorInfo): &Option<TableVec<vector<u8>>> {
    validator_info::next_epoch_mpc_data_bytes(self)
}

#[spec(prove, target = validator_info::previous_mpc_data_bytes, ignore_abort)]
fun previous_mpc_data_bytes_spec(self: &ValidatorInfo): &Option<TableVec<vector<u8>>> {
    validator_info::previous_mpc_data_bytes(self)
}