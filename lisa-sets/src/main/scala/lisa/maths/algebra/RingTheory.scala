package lisa.maths.algebra

import lisa.maths.algebra.GroupTheory.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.functions.Functionals.* 
import lisa.automation.kernel.CommonTactics.Definition

object RingTheory extends lisa.Main {
    // Operations
    private val + = variable
    private val * = variable

    // Ring elements
    private val x, y, z = variable

    // Identity elements
    private val e = variable

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
    private val distributivityAxiom = DEF(G, +, *) -->
        ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) 
                                                        /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z)))))))

    /**
    * Ring --- A ring (G, +, *) is a set along with a law of composition `*` and '+', satisfying [[abelianGroup]], [[closedByProducts]],
    * [[associativityAxiom]], [[identityExistence]] and [[distributivityAxiom]].
    */
    val ring = DEF(G, +, *) --> group(G, +) /\ abelianGroup(G, +) /\ closedByProducts /\ associativityAxiom(G, *) 
                                /\ identityExistence(G, *) /\ distributivityAxiom(G, *, +)

    /**
    * Commutative ring --- A ring is said to be commutative if every element commutes under '*',
    * i.e. it satisfies [[commutativityAxiom]].
    */
    val commutativeRing = DEF(G, +, *) --> ring(G, +, *) /\ commutativityAxiom(G, *)

    /**
    * Identity uniqueness --- In a ring (G, +, *), an identity element is unique, i.e. if both `e + x = x + e = x` and
    * `f + x = x + f = x` for all `x`, then `e = f`.
    *
    * This justifies calling `e` <i>the</i> identity element.
    */
    val additiveIdentityUniqueness = Theorem(ring(G, +, *) |- ∃!(e, isNeutral(e, G, +))) {
        assume(ring(G, +, *))
        have(thesis) by Tautology.from(ring.definition, identityUniqueness of (G -> G, * -> +))
    }

    /**
    * Theorem --- The additive inverse of an element `x` (i.e. `y` such that `x + y = y + x = e`) in `G` is unique.
    */
    val additiveInverseUniqueness = Theorem((ring(G, +, *), x ∈ G) |- ∃!(y, isInverse(y, x, G, +)) ){
        assume(ring(G, +, *), x ∈ G)
        have(thesis) by Tautology.from(ring.definition, inverseUniqueness of (G -> G, * -> +))
    }
    

}
