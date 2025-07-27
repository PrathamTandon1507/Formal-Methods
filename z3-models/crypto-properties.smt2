; Cryptographic Key Management Verification
; Models key lifecycle and encryption properties

(set-logic QF_LIA)

; Key states and properties
(declare-const key_id Int)
(declare-const key_strength Int)
(declare-const key_age Int)
(declare-const key_usage_count Int)

; Key lifecycle states
(declare-const KEY_GENERATED Int)
(declare-const KEY_ACTIVE Int)
(declare-const KEY_EXPIRED Int)
(declare-const KEY_REVOKED Int)

(assert (= KEY_GENERATED 1))
(assert (= KEY_ACTIVE 2))
(assert (= KEY_EXPIRED 3))
(assert (= KEY_REVOKED 4))

(declare-const key_state Int)

; Encryption parameters
(declare-const plaintext_size Int)
(declare-const ciphertext_size Int)
(declare-const encryption_overhead Int)

; Security requirements
; Minimum key strength for defense applications
(assert (>= key_strength 256))  ; 256-bit minimum

; Key rotation policy
(declare-const max_key_age Int)
(declare-const max_usage_count Int)

(assert (= max_key_age 30))      ; 30 days maximum
(assert (= max_usage_count 1000)) ; 1000 operations maximum

; Key lifecycle constraints
(assert (>= key_age 0))
(assert (>= key_usage_count 0))

; Active key constraints
(assert (=> (= key_state KEY_ACTIVE)
            (and (<= key_age max_key_age)
                 (<= key_usage_count max_usage_count))))

; Expired key detection
(assert (=> (or (> key_age max_key_age)
                (> key_usage_count max_usage_count))
            (= key_state KEY_EXPIRED)))

; Encryption size relationship
(assert (> plaintext_size 0))
(assert (= ciphertext_size (+ plaintext_size encryption_overhead)))
(assert (>= encryption_overhead 16))  ; Minimum IV + MAC

; Security property: No encryption with expired keys
(assert (not (and (= key_state KEY_EXPIRED)
                  (> ciphertext_size plaintext_size))))

; Test scenario: Key approaching expiration
(assert (= key_strength 256))
(assert (= key_age 29))
(assert (= key_usage_count 999))
(assert (= key_state KEY_ACTIVE))
(assert (= plaintext_size 100))
(assert (= encryption_overhead 32))

(check-sat)
(get-model)