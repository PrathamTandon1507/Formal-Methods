// Simple Security Policy Model

module security_policy

// Security levels
enum SecurityLevel { Public, Confidential, Secret }

// Users with clearance
sig User {
    name: one String,
    clearance: one SecurityLevel
}

// Documents with classification
sig Document {
    name: one String,
    classification: one SecurityLevel
}

// Access attempts
sig Access {
    user: one User,
    document: one Document,
    allowed: one Bool
}

// Security rules
fact SecurityRules {
    // Access control based on clearance level
    all a: Access |
        a.allowed = True iff canAccess[a.user, a.document]
}

// Access predicate
pred canAccess[u: User, d: Document] {
    // User clearance must be >= document classification
    (u.clearance = Secret) or
    (u.clearance = Confidential and d.classification != Secret) or
    (u.clearance = Public and d.classification = Public)
}

// Example scenario
pred SecurityExample {
    some alice, bob: User |
    some doc1, doc2: Document |
    some access1, access2: Access | {
        // Users
        alice.name = "alice"
        alice.clearance = Secret
        bob.name = "bob"
        bob.clearance = Public
        
        // Documents
        doc1.name = "public_memo"
        doc1.classification = Public
        doc2.name = "classified_report"
        doc2.classification = Secret
        
        // Access attempts
        access1.user = alice
        access1.document = doc2
        access1.allowed = True  // Alice can access secret doc
        
        access2.user = bob
        access2.document = doc2
        access2.allowed = False  // Bob cannot access secret doc
    }
}

run SecurityExample for 5