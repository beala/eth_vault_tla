(* This models a smart contract that acts as a vault for ethereum funds.
   The vault starts in a locked state with some amount of ether. In order
   to withdraw funds, the user must provide a secret key which will
   transition that vault into an unlocked state. After a waiting period,
   the vault can move to a withdrawal state where the funds are disbursed.
   
   The vault also has a recovery key. With the recovery key, if the vault 
   is in the unlocked state, it can be re-keyed with a new key and sent
   back to the locked state. The recovery key can also be used to destroy
   the vault, taking the funds with it.
   
   The contract is modeled as a state machine that processes a queue of messages.
   Invariants are verified against every possible message queue of length n.
   For n >= 5, the problem becomes intractable.
   
   With a max of 4 messages, there are some valid and important transitions that
   are left out. For example:
   
   Locked -> Unlocked -> Rekeyed -> Unlocked -> Withdrawn
   
   There are many possible ways I could restrict the state space:
   
   - If the set of keys the user has is made static (in other words, it models only 
     a single user interacting with the vault), n can be larger.
   
   - Only create message queues that have commands in a valid order (ie, withdraw 
     always comes after unlock), but this would not test the state transition
     precondition logic.
     
   - Only test single transitions. For example, validate that only a valid message
     can transition the vault from the Locked to Unlocked state. Then do the same
     thing for the Unlocked -> Withdrawn transition and so on. This avoids the
     exponential blowup.
   
   
*)
------------------------------- MODULE eth_vault -------------------------------
EXTENDS Sequences, Integers, TLC

\* The commands that can be sent to the contract
CONSTANTS WITHDRAW, UNLOCK, DESTROY, LOCK, NOP, DEPOSIT, REKEY

\* The possible states of the contract
CONSTANTS WITHDRAWN_STATE, UNLOCKED_STATE, DESTROYED_STATE, LOCKED_STATE

\* Keys required to use the contract.
CONSTANTS UNLOCK_KEY, RECOVERY_KEY, NEW_UNLOCK_KEY

CONSTANTS STARTING_BALANCE

(* --algorithm eth_vault
\* The starting balance of the vault.
variable balance = STARTING_BALANCE, 
          \* The starting state
          state = LOCKED_STATE,
          \* The block after which money can be withdrawn (enforces the waiting period).
          withdrawAfter = 0,
          \* The current block
          block = 0,
          unlockKey = UNLOCK_KEY,
          \* A specific set of keys. Can be used to model a single user interacting
          \* with the vault.
          chosenKeys \in Keys,
          \* After a message is processed, it's added to this log.
          \* Invariants are checked against it.
          messageLog = <<>>,
          curMsg = 1,
          rekeyed = FALSE;

define
    \* Return the elements of a tuple as a set
    Range(t) == {t[i] : i \in DOMAIN t}
    
    Min(x,y) == IF x > y THEN y ELSE x
                
    \* All possible sets of keys
    Keys == SUBSET {UNLOCK_KEY, RECOVERY_KEY, NEW_UNLOCK_KEY}

    \* All possible messages for a given key set `k`
    WithdrawMessages(ks) =={[instr |-> WITHDRAW, keys |-> k, amount |-> i] : i \in -1..1, k \in ks}
    UnlockMessages(ks) ==  {[instr |-> UNLOCK,   keys |-> k]: k \in ks}
    DestroyMessages(ks) == {[instr |-> DESTROY,  keys |-> k]: k \in ks}
    LockMessages(ks) ==    {[instr |-> LOCK,     keys |-> k]: k \in ks}
    RekeyMessages(ks) ==   {[instr |-> REKEY,    keys |-> k]: k \in ks}
    \* Keys don't matter for deposits so k |-> {}
    DepositMessages ==    {[instr |-> DEPOSIT,   keys |-> {}, amount |-> i] : i \in -1..1}
    
    AllPossibleMessages(k) == WithdrawMessages(k) \union 
                              UnlockMessages(k) \union 
                              DestroyMessages(k) \union 
                              LockMessages(k) \union 
                              RekeyMessages(k) \union
                              DepositMessages
                           
    \* All possible messages queues of length `n` with a set of keys chosen from `k`.
    MessageQueues(n, k) == [1..n -> AllPossibleMessages(k)]
end define;

(* This models the contract. It reads messages off the messages
   queue and services them in order.
*)
process Vault = 0
variables 
    msg = NOP,
    \* messages \in MessageQueues(4, {chosenKeys}),
    messages \in MessageQueues(4, Keys);
begin
    \* Each iteration of the loop processes a single message
    \* from the `messages` queue. Each iteration happens as
    \* an atomic step (ie, a block is mined).
    Start:
    while curMsg <= Len(messages) do
        msg := messages[curMsg];
        
        \* messageLog := Append(messageLog, [msg |-> msg, unlockKey |-> unlockKey]);

        \* Each `if` branch services a specific command and checks
        \* preconditions.
        if /\ msg.instr = WITHDRAW 
           /\ state = UNLOCKED_STATE
           /\ unlockKey \in msg.keys 
           /\ msg.amount <= balance 
           /\ block > withdrawAfter 
        then
            balance := balance - msg.amount
            
        elsif /\ msg.instr = UNLOCK 
              /\ state = LOCKED_STATE
              /\ unlockKey \in msg.keys
        then
            state := UNLOCKED_STATE;
            \* After it's unlocked, there is a waiting
            \* period of 1 block to relock, rekey, or
            \* destroy.
            withdrawAfter := block + 2;

        elsif /\ msg.instr = DESTROY 
              /\ \/ state = LOCKED_STATE
                 \/ state = UNLOCKED_STATE
              /\ RECOVERY_KEY \in msg.keys 
        then
            state := DESTROYED_STATE;
            balance := 0
            
        elsif /\ msg.instr = REKEY 
              /\ \/ state = LOCKED_STATE
                 \/ state = UNLOCKED_STATE
              /\ RECOVERY_KEY \in msg.keys
        then
            unlockKey := NEW_UNLOCK_KEY;
            state := LOCKED_STATE;
            rekeyed := TRUE;
            
        elsif /\ msg.instr = LOCK
              /\ state = UNLOCKED_STATE
              /\ RECOVERY_KEY \in msg.keys 
        then
            state := LOCKED_STATE;
            
        elsif /\ msg.instr = DEPOSIT
              /\ msg.amount >= 0
              /\ state /= DESTROYED_STATE
        then
            balance := balance + msg.amount

        end if;
        
        block := block + 1;
        curMsg := curMsg + 1;
        
    end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
VARIABLES balance, state, withdrawAfter, block, unlockKey, chosenKeys, 
          messageLog, curMsg, rekeyed, pc

(* define statement *)
Range(t) == {t[i] : i \in DOMAIN t}

Min(x,y) == IF x > y THEN y ELSE x


Keys == SUBSET {UNLOCK_KEY, RECOVERY_KEY, NEW_UNLOCK_KEY}


WithdrawMessages(ks) =={[instr |-> WITHDRAW, keys |-> k, amount |-> i] : i \in -1..1, k \in ks}
UnlockMessages(ks) ==  {[instr |-> UNLOCK,   keys |-> k]: k \in ks}
DestroyMessages(ks) == {[instr |-> DESTROY,  keys |-> k]: k \in ks}
LockMessages(ks) ==    {[instr |-> LOCK,     keys |-> k]: k \in ks}
RekeyMessages(ks) ==   {[instr |-> REKEY,    keys |-> k]: k \in ks}

DepositMessages ==    {[instr |-> DEPOSIT,   keys |-> {}, amount |-> i] : i \in -1..1}

AllPossibleMessages(k) == WithdrawMessages(k) \union
                          UnlockMessages(k) \union
                          DestroyMessages(k) \union
                          LockMessages(k) \union
                          RekeyMessages(k) \union
                          DepositMessages


MessageQueues(n, k) == [1..n -> AllPossibleMessages(k)]

VARIABLES msg, messages

vars == << balance, state, withdrawAfter, block, unlockKey, chosenKeys, 
           messageLog, curMsg, rekeyed, pc, msg, messages >>

ProcSet == {0}

Init == (* Global variables *)
        /\ balance = STARTING_BALANCE
        /\ state = LOCKED_STATE
        /\ withdrawAfter = 0
        /\ block = 0
        /\ unlockKey = UNLOCK_KEY
        /\ chosenKeys \in Keys
        /\ messageLog = <<>>
        /\ curMsg = 1
        /\ rekeyed = FALSE
        (* Process Vault *)
        /\ msg = NOP
        /\ messages \in MessageQueues(4, Keys)
        /\ pc = [self \in ProcSet |-> "Start"]

Start == /\ pc[0] = "Start"
         /\ IF curMsg <= Len(messages)
               THEN /\ msg' = messages[curMsg]
                    /\ IF /\ msg'.instr = WITHDRAW
                          /\ state = UNLOCKED_STATE
                          /\ unlockKey \in msg'.keys
                          /\ msg'.amount <= balance
                          /\ block > withdrawAfter
                          THEN /\ balance' = balance - msg'.amount
                               /\ UNCHANGED << state, withdrawAfter, unlockKey, 
                                               rekeyed >>
                          ELSE /\ IF /\ msg'.instr = UNLOCK
                                     /\ state = LOCKED_STATE
                                     /\ unlockKey \in msg'.keys
                                     THEN /\ state' = UNLOCKED_STATE
                                          /\ withdrawAfter' = block + 2
                                          /\ UNCHANGED << balance, unlockKey, 
                                                          rekeyed >>
                                     ELSE /\ IF /\ msg'.instr = DESTROY
                                                /\ \/ state = LOCKED_STATE
                                                   \/ state = UNLOCKED_STATE
                                                /\ RECOVERY_KEY \in msg'.keys
                                                THEN /\ state' = DESTROYED_STATE
                                                     /\ balance' = 0
                                                     /\ UNCHANGED << unlockKey, 
                                                                     rekeyed >>
                                                ELSE /\ IF /\ msg'.instr = REKEY
                                                           /\ \/ state = LOCKED_STATE
                                                              \/ state = UNLOCKED_STATE
                                                           /\ RECOVERY_KEY \in msg'.keys
                                                           THEN /\ unlockKey' = NEW_UNLOCK_KEY
                                                                /\ state' = LOCKED_STATE
                                                                /\ rekeyed' = TRUE
                                                                /\ UNCHANGED balance
                                                           ELSE /\ IF /\ msg'.instr = LOCK
                                                                      /\ state = UNLOCKED_STATE
                                                                      /\ RECOVERY_KEY \in msg'.keys
                                                                      THEN /\ state' = LOCKED_STATE
                                                                           /\ UNCHANGED balance
                                                                      ELSE /\ IF /\ msg'.instr = DEPOSIT
                                                                                 /\ msg'.amount >= 0
                                                                                 /\ state /= DESTROYED_STATE
                                                                                 THEN /\ balance' = balance + msg'.amount
                                                                                 ELSE /\ TRUE
                                                                                      /\ UNCHANGED balance
                                                                           /\ state' = state
                                                                /\ UNCHANGED << unlockKey, 
                                                                                rekeyed >>
                                          /\ UNCHANGED withdrawAfter
                    /\ block' = block + 1
                    /\ curMsg' = curMsg + 1
                    /\ pc' = [pc EXCEPT ![0] = "Start"]
               ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                    /\ UNCHANGED << balance, state, withdrawAfter, block, 
                                    unlockKey, curMsg, rekeyed, msg >>
         /\ UNCHANGED << chosenKeys, messageLog, messages >>

Vault == Start

Next == Vault
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\****************** INVARIANTS ********************

\* Balance must always be positive
PositiveBalance == balance >= 0

\* Balance cannot go down unless there is a valid withdraw or destroy command.
NoLeak ==  
    balance < STARTING_BALANCE =>  
        \E m \in Range(SubSeq(messages, 1, Min(curMsg, Len(messages)))) : 
             \/ /\ UNLOCK_KEY \in m.keys 
                /\ m.instr = WITHDRAW 
                /\ ~rekeyed
             \/ /\ RECOVERY_KEY \in m.keys 
                /\ m.instr = DESTROY
             \/ /\ NEW_UNLOCK_KEY \in m.keys 
                /\ m.instr = WITHDRAW 
                /\ rekeyed

\* Can't unlock without unlock key
NoUnlock == 
    state = UNLOCKED_STATE =>  
        \E m \in Range(SubSeq(messages, 1, Min(curMsg, Len(messages)))) : 
            \/ /\ ~rekeyed
               /\ UNLOCK_KEY \in m.keys
               /\ m.instr = UNLOCK
            \/ /\ rekeyed
               /\ NEW_UNLOCK_KEY \in m.keys
               /\ m.instr = UNLOCK

\* Can't withdraw without valid unlock key
NoWithdraw ==
    state = UNLOCKED_STATE =>  
        \E m \in Range(SubSeq(messages, 1, Min(curMsg, Len(messages)))) : 
            \/ /\ ~rekeyed
               /\ UNLOCK_KEY \in m.keys
               /\ m.instr = UNLOCK
            \/ /\ rekeyed
               /\ NEW_UNLOCK_KEY \in m.keys
               /\ m.instr = UNLOCK

\* Can't re-key without the recovery key.
NoRekey ==
    unlockKey = NEW_UNLOCK_KEY =>  
        \E m \in Range(SubSeq(messages, 1, Min(curMsg, Len(messages)))) : 
            /\ RECOVERY_KEY \in m.keys
            /\ m.instr = REKEY

\* Can't destroy without recovery key.
NoDestroy ==
    state = DESTROYED_STATE =>  
        \E m \in Range(SubSeq(messages, 1, Min(curMsg, Len(messages)))) : 
            /\ RECOVERY_KEY \in m.keys
            /\ m.instr = DESTROY

=============================================================================
\* Modification History
\* Last modified Sat Feb 17 11:33:55 MST 2018 by alex
\* Created Thu Feb 15 14:38:20 MST 2018 by alex
