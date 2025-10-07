module specs::staked_ika_specs;

use ika_system::staked_ika::{Self, StakedIka};

#[spec(prove, target = staked_ika::validator_id, ignore_abort)]
public fun validator_id_spec(sw: &StakedIka): ID {
    staked_ika::validator_id(sw)
}

#[spec(prove, target = staked_ika::value, ignore_abort)]
public fun value_spec(sw: &StakedIka): u64 {
    staked_ika::value(sw)
}

#[spec(prove, target = staked_ika::activation_epoch, ignore_abort)]
public fun activation_epoch_spec(sw: &StakedIka): u64 {
    staked_ika::activation_epoch(sw)
}

#[spec(prove, target = staked_ika::is_staked, ignore_abort)]
public fun is_staked_spec(sw: &StakedIka): bool {
    staked_ika::is_staked(sw)
}

#[spec(prove, target = staked_ika::is_withdrawing, ignore_abort)]
public fun is_withdrawing_spec(sw: &StakedIka): bool {
    staked_ika::is_withdrawing(sw)
}

#[spec(prove, target = staked_ika::withdraw_epoch, ignore_abort)]
public fun withdraw_epoch_spec(sw: &StakedIka): u64 {
    staked_ika::withdraw_epoch(sw)
}

#[spec(prove, target = staked_ika::join, ignore_abort)]
public fun join_spec(sw: &mut StakedIka, other: StakedIka) {
    staked_ika::join(sw, other)
}

#[spec(prove, target = staked_ika::split, ignore_abort)]
fun split_spec(sw: &mut StakedIka, amount: u64, ctx: &mut TxContext): StakedIka {
    staked_ika::split(sw, amount, ctx)
}