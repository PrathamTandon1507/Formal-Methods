; Banking System Transaction Verification
; Models transaction integrity and balance conservation

(set-logic QF_LIA)

; Account balances before transaction
(declare-const account_a_initial Int)
(declare-const account_b_initial Int)

; Account balances after transaction
(declare-const account_a_final Int)
(declare-const account_b_final Int)

; Transaction parameters
(declare-const transfer_amount Int)
(declare-const transaction_fee Int)

; Initial conditions - realistic account balances
(assert (= account_a_initial 5000))  ; Account A starts with 5000
(assert (= account_b_initial 2000))  ; Account B starts with 2000
(assert (> transfer_amount 0))       ; Positive transfer amount
(assert (<= transfer_amount 1000))   ; Reasonable transfer limit
(assert (>= transaction_fee 0))      ; Non-negative fee
(assert (<= transaction_fee 50))     ; Reasonable fee limit

; Sufficient funds check
(assert (>= account_a_initial (+ transfer_amount transaction_fee)))

; Transaction execution - balance updates
(assert (= account_a_final (- account_a_initial (+ transfer_amount transaction_fee))))
(assert (= account_b_final (+ account_b_initial transfer_amount)))

; Critical property: No negative balances (overdraft protection)
(assert (>= account_a_final 0))
(assert (>= account_b_final 0))

; Conservation property: Total money preserved (accounting for fees)
(declare-const total_initial Int)
(declare-const total_final_plus_fees Int)

(assert (= total_initial (+ account_a_initial account_b_initial)))
(assert (= total_final_plus_fees (+ account_a_final account_b_final transaction_fee)))
(assert (= total_initial total_final_plus_fees))

; Audit trail: Transaction bounds
(assert (>= transfer_amount 10))     ; Minimum transaction
(assert (<= transfer_amount 500))    ; Maximum for this test

(check-sat)
(get-model)