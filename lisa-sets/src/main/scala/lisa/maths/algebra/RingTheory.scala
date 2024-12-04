package lisa.maths.algebra

import lisa.maths.algebra.GroupTheory.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.functions.Functionals.* 

object RingTheory extends lisa.Main {
    // Operations
    private val + = variable
    private val * = variable

    // Ring elements
    private val x, y, z = variable

    // Group in the ring
    private val G = variable

    /**
    * Short-hand alias for `x operator y`.
    * In ring context we have x*y or x+y
    */
    inline def op(x: Term, operator : Term, y: Term) = app(operator, pair(x, y))
    
    // Useful Lemma to define closure
    private val closedByProducts = ∀(x, ∀(y, (x ∈ G /\ y ∈ G) ==> (op(x, *, y) ∈ G)))
    
    /**
    * Distributivity --- `*,+` are distributive (in `R`) if `x * (y + z) = x * y + x * z 
    * and (x + y) * z = x * z + y * z ` for all `x, y, z` in `R`.
    */
    private val distributivityAxiom = DEF(G, *, +) -->
        ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) 
                                                        /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z)))))))

    /**
    * Ring --- A ring (G, *, +) is a set along with a law of composition `*` and '+', satisfying [[abelianGroup]], [[closedByProducts]],
    * [[associativityAxiom]], [[identityExistence]] and [[distributivityAxiom]].
    */
    val ring = DEF(G, *, +) --> abelianGroup(G, +) /\ closedByProducts /\ associativityAxiom(G, *) 
                                /\ identityExistence(G, *) /\ distributivityAxiom(G, *, +)
    

}
