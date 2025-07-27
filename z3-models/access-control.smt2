; Access Control System Verification
; Verifies role-based access control properties with privilege escalation detection

(set-logic QF_LIA)

; User and Role declarations
(declare-const admin_user Int)
(declare-const regular_user Int)
(declare-const guest_user Int)

; Resource access levels
(declare-const read_permission Int)
(declare-const write_permission Int)
(declare-const execute_permission Int)

; Role hierarchy constants
(declare-const admin_role Int)
(declare-const user_role Int)
(declare-const guest_role Int)

; Define role hierarchy: admin > user > guest
(assert (= admin_role 3))
(assert (= user_role 2))
(assert (= guest_role 1))

; Permission levels: execute > write > read
(assert (= execute_permission 3))
(assert (= write_permission 2))
(assert (= read_permission 1))

; User-Role assignments
(assert (= admin_user admin_role))
(assert (= regular_user user_role))
(assert (= guest_user guest_role))

; Access control rules
; Admin can access all permissions
(assert (>= admin_role execute_permission))

; Regular user can read and write but not execute
(assert (>= user_role write_permission))
(assert (< user_role execute_permission))

; Guest can only read
(assert (>= guest_role read_permission))
(assert (< guest_role write_permission))

; Security property verification: Privilege escalation attempt
(declare-const malicious_user Int)
(declare-const requested_permission Int)

; Simulate a user trying to access beyond their privilege level
(assert (= malicious_user guest_role))
(assert (= requested_permission execute_permission))

; This assertion should make the formula UNSAT (proving security)
(assert (>= malicious_user requested_permission))

; Check satisfiability - should be UNSAT for secure system
(check-sat)