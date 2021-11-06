(* Token Creator smart contract that implements the Fa2 standard *)





type token_id = nat
type name = string

// fa2 types
type operator_param =
[@layout:comb]
{
  owner : address;
  operator : address;
  token_id : token_id;
}

type update_operator =
  [@layout:comb]
  | Add_operator of operator_param
  | Remove_operator of operator_param

type balance_of_request =
[@layout:comb]
{
  owner : address;
  token_id : token_id;
}

type balance_of_response =
[@layout:comb]
{
  request : balance_of_request;
  balance : nat;
}

type balance_of_param =
[@layout:comb]
{
  requests : balance_of_request list;
  callback : (balance_of_response list) contract;
}

type transfer_destination =
[@layout:comb]
{
  to_ : address;
  token_id : token_id;
  amount : nat;
}

type transfer =
[@layout:comb]
{
  from_ : address;
  txs : transfer_destination list;
}

// stores the balance of each unique token and addresses
type ledger = ((token_id * address), nat) map

type token_total_supply = (token_id, nat) map
type available_token_supply = (token_id, nat) map

// stores valid operators as a list of addresses
type operator_storage = ((token_id * address), address list) map

type token_metadata = {token_id: token_id; name: string; decimals: nat; owner: address}
type token_metadata_storage = (token_id, token_metadata) map

// the main storage, keeps track of all the tokens and relevant info involving them
type multiple_token_storage = {
  ledger : ledger;
  operators : operator_storage;
  token_total_supply : token_total_supply;
  available_token_supply : available_token_supply;
  token_metadata : token_metadata_storage;
  number_of_tokens: nat
}


(*
    helper function that confirms if a token id exists
*)
let confirm_token (id, supply: token_id * token_total_supply ): bool = 
    match Map.find_opt id supply with 
    Some _t -> true
    | None -> (failwith "FA2_TOKEN_UNDEFINED" : bool)

(*
    super simple helper function that gets a specific token's balance  against
    a specific user from the ledger
*)
let _get_balance (token_id, addrs, ledger: token_id * address * ledger): nat = 
    let bal : nat =  
        match Map.find_opt (token_id, addrs) ledger with
        Some b -> b
        | None -> 0n
    in bal
    
(*
    deduct an amount from a account / token pair if possible else fail
*)
let remove_from_balance (token_id, deductable, source_address, ledger: token_id * nat * address * ledger): ledger = 
    let key : (token_id * address) =  (token_id, source_address)
    in

    let bal : nat =  _get_balance (key.0, key.1, ledger)
    in

    if bal < deductable then (failwith "FA2_INSUFFICIENT_BALANCE" : ledger)
    else

    Map.update
    (key : token_id * address) (Some (abs (bal - deductable)) ) ledger

(*
    add amount to a specific account/id pair, create a mapping and add amount
    if it did not already exist
*)
let add_to_balance (token_id, addition, dest_address, ledger: token_id * nat * address * ledger): ledger = 
    let key : (token_id * address) =  (token_id, dest_address)
    in

    let bal : nat =  _get_balance (key.0, key.1, ledger)
    in

    if bal = 0n then Map.add (key : token_id * address) addition ledger
    else Map.update
        (key : token_id * address) (Some (bal + addition) ) ledger

(*
    get balance function that is used to get a balance_of_response object
    that contains a specific balance 
*)
let get_balance (single_request, ledger, supply: balance_of_request * ledger * token_total_supply): balance_of_response = 
    let key : (token_id * address) =  (single_request.token_id, single_request.owner)
    in

    let valid: bool = confirm_token (key.0, supply)
    in
    {
        request = single_request;
        balance = _get_balance (key.0, key.1, ledger);
    }

(*
    handle batch balance operations
*)
let balances (params, ledger, supply: balance_of_param * ledger * token_total_supply): operation =
    let responses: balance_of_response list = 
        List.map 
        (fun (req: balance_of_request) -> get_balance (req, ledger, supply)) params.requests
        in
        Tezos.transaction responses 0mutez params.callback

(*
    handle a single transfer operation as specified by the fa2 standard, 
    only allow transfers if the caller is the owner of the account or is authorised to 
    transfer
*)
let handle_single_transfer (transfer, op_store, ledger, supply: transfer * operator_storage * ledger * token_total_supply): ledger = 
    let is_an_operator (sender_addrs, operators: address * address list): bool = 
        List.fold_left (fun (acc, single_op: bool * address) -> 
            if acc = true then acc 
            else
                if single_op = sender_addrs then true else false)
            false operators
    in 

    let is_authorised (token_id: token_id) : bool = 
        (   let operators : address list =   
                match Map.find_opt (token_id, transfer.from_) op_store with
                Some o -> o
                | None -> (failwith "wasnt found" : address list)
            in

            if Tezos.sender = transfer.from_ || is_an_operator (Tezos.sender, operators) then true
                else (failwith "FA2_NOT_OPERATOR" : bool)
        )
    in

    List.fold_left (fun (acc, tx:ledger * transfer_destination) -> (
                        let checks: bool =  (confirm_token (tx.token_id, supply) && is_authorised tx.token_id) in
                        let temp_ledger: ledger = remove_from_balance (tx.token_id, tx.amount, transfer.from_, acc) in
                        add_to_balance (tx.token_id, tx.amount, tx.to_, temp_ledger)    
                    )) ledger transfer.txs


(*
    handle batch transfer
*)
let transfer (transfers, ledger, op_store, supply: transfer list * ledger * operator_storage * token_total_supply): ledger = 
    List.fold_left (fun (acc, transfer: ledger * transfer) -> 
                        handle_single_transfer  (transfer, op_store, acc, supply)
                    ) ledger transfers


(*
    add an operator to a token/pair operator list
*)
let add_operator (op_param, op_storage: operator_param * operator_storage): operator_storage = 
    
    let key : (token_id * address) =  (op_param.token_id, op_param.owner)
    in

    let current_operators : address list =   
        match Map.find_opt key op_storage with
        Some o -> o
        | None -> ([]: address list)
    in

    let updated_operators : address list = op_param.operator :: current_operators
    in

    Map.update
    (key : token_id * address) (Some updated_operators) op_storage

(*
    remove an operator from a token/pair operator list
*)
let remove_operator (op_param, op_storage: operator_param * operator_storage): operator_storage = 
    
    let key : (token_id * address) =  (op_param.token_id, op_param.owner)
    in

    let current_operators : address list =   
        match Map.find_opt key op_storage with
        Some o -> o
        | None -> (failwith "wasnt found" : address list)
    in

    let delete (addrs, acc: address * address list) = 
        if addrs = op_param.operator then acc else addrs::acc
    in

    let updated_operators : address list = 
        List.fold_right delete current_operators ([]: address list) 
    in

    Map.update
    (key : token_id * address) (Some updated_operators) op_storage

(*
    handle bulk add or remove operations
*)
let update_operators (operators, op_storage: update_operator list * operator_storage): operator_storage =
    
    let single_update (op, new_opstore: update_operator * operator_storage ): operator_storage = 
        match op with
        | Add_operator (op_param) -> add_operator (op_param, new_opstore)
        | Remove_operator (op_param) -> remove_operator (op_param, new_opstore)
    in
    
    List.fold_left (fun (acc, single_op: operator_storage * update_operator) -> 
                single_update (single_op, acc)) (op_storage: operator_storage) operators


(*
    function that allows a transaction sender to create a new FA2 (ERC20) standard token
*)
let create_token (name, decimals, supply, token_store: name * nat * nat * multiple_token_storage): multiple_token_storage = 
    let id: token_id = token_store.number_of_tokens + 1n 
    in
    let meta: token_metadata = {token_id = id; name = name; decimals = decimals;
                                    owner=Tezos.sender;
                                }
    in

    let update_metadata: token_metadata_storage = Map.add (id) (meta) token_store.token_metadata
    in
    
    let total_supply: token_total_supply = Map.add (id) (supply) token_store.token_total_supply
    in
    
    let available_supply: available_token_supply = Map.add (id) (supply) token_store.available_token_supply
    in

    {token_store with token_metadata=update_metadata; token_total_supply=total_supply;
        available_token_supply=available_supply; number_of_tokens=id;
        }


(*
    allocate a specified amount of a token to an account, if the available supply is not yet 
    exhausted, can only be called by the owner of a token
*)
let mint_token (id, quantity, dest_address, token_store: token_id * nat * address * multiple_token_storage): multiple_token_storage = 
    
    let meta: token_metadata = match Map.find_opt id (token_store.token_metadata) with 
                                    Some m -> m
                                    |None -> (failwith "invalid":token_metadata)
    in

    if (not (Tezos.sender = meta.owner)) then (failwith "not authorised to mint": multiple_token_storage)
    else
    let current_supply: nat = match Map.find_opt id token_store.available_token_supply with
                                Some s -> s
                                |None -> (failwith ("invalid"): nat)
    in 

    if current_supply < quantity then (failwith "not enough supply left": multiple_token_storage)
    else
    let new_available_supply: available_token_supply = Map.update id (Some (abs (current_supply - quantity))) token_store.available_token_supply
    in

    let newledger: ledger = add_to_balance (id, quantity, dest_address, token_store.ledger)
    in

    {token_store with available_token_supply=new_available_supply; ledger=newledger;}

(*
    all the entry points for the contract, the standard fa2 ones and 2 extra that allows for token
    for token creation and mint operations
*)
type entry = 
    | Update_operators of update_operator list
    | Balance_of of balance_of_param
    | Transfer of transfer list
    | Create_token of {name: name; decimals: nat; supply: nat}
    | Mint_token of {token_id: token_id; amount: nat; destination_addrs: address}


let main (action, token_store : entry * multiple_token_storage) : operation list * multiple_token_storage =
 
    match action with

        | Transfer txns ->
            let newledger:ledger = (transfer (txns, token_store.ledger, token_store.operators, token_store.token_total_supply))
            in
            (([]:operation list), {token_store with ledger=newledger})

        | Balance_of bal_txns -> 
            let op:operation = balances (bal_txns, token_store.ledger, token_store.token_total_supply)
            in 
            (([op]:operation list), token_store)

        | Update_operators ops ->
            let new_operators: operator_storage = update_operators (ops, token_store.operators)
            in
            (([]:operation list), {token_store with operators=new_operators})

        | Create_token r ->
            (([]:operation list), create_token (r.name, r.decimals, r.supply, token_store))
        
        | Mint_token r ->
            (([]:operation list), mint_token (r.token_id, r.amount, r.destination_addrs, token_store))






