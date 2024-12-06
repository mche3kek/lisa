package lisa.maths.algebra

import lisa.maths.algebra.GroupTheory.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.functions.Functionals.* 
import lisa.maths.Quantifiers.*
import lisa.automation.kernel.CommonTactics.Definition
import lisa.automation.kernel.CommonTactics.ExistenceAndUniqueness

object RingTheory extends lisa.Main {
    // Operations
    private val + = variable
    private val * = variable

    // Ring elements
    private val x, y, z = variable

    // Identity elements
    private val e, f = variable

    // Group in the ring
    private val G, H, U = variable

    /**
     * Short-hand alias for `x operator y`.
     * In ring context we have x*y or x+y
     */
    inline def op(x: Term, operator : Term, y: Term) = app(operator, pair(x, y))
    
    //
    // 1. Basic definitions and results
    //

    // Useful Lemmas
    val closure = DEF(G, *) --> ∀(x, ∀(y, (x ∈ G /\ y ∈ G) ==> (op(x, *, y) ∈ G)))
    private val absorbingElementZero = isNeutral(e, G, +) ==> ∀(x, x ∈ G ==> (op(x, *, e) === e) /\ (op(e, *, x) === e))
    
    /**
     * Distributivity --- `*,+` are distributive (in `R`) if `x * (y + z) = x * y + x * z 
     * and (x + y) * z = x * z + y * z ` for all `x, y, z` in `R`.
     */
    private val distributivityAxiom = DEF(G, +, *) -->
        ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) 
                                                        /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z)))))))

    /**
     * Ring --- A ring (G, +, *) is a set along with a law of composition `*` and '+', satisfying [[abelianGroup]], [[closure]],
     * [[associativityAxiom]], [[identityExistence]] and [[distributivityAxiom]].
     */
    val ring = DEF(G, +, *) --> group(G, +) /\ abelianGroup(G, +) /\ closure(G, *) /\ associativityAxiom(G, *) 
                                /\ distributivityAxiom(G, *, +)

    /**
     * Ring with identity --- A ring with identity (G, +, *) is a ring containing an identity element under '*', satisfying [[identityExistence]].
     */
    val identityRing = DEF(G, +, *) --> ring(G, +, *) /\ identityExistence(G, *)
    
    /**
     * Commutative ring --- A ring is said to be commutative if every element commutes under '*',
     * i.e. it satisfies [[commutativityAxiom]].
     */
    val commutativeRing = DEF(G, +, *) --> ring(G, +, *) /\ commutativityAxiom(G, *)

    /**
     * Additive Identity uniqueness --- In a ring (G, +, *), an additive identity element is unique, i.e. if both `e + x = x + e = x` and
     * `f + x = x + f = x` for all `x`, then `e = f`.
     *
     * This justifies calling `e` <i>the</i> additive identity element.
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

    /**
     * Multiplicative identity uniqueness --- In a ring with identity (G, +, *), a multiplicative identity element is unique, 
     * i.e. if both `e * x = x * e = x` and `f * x = x * f = x` for all `x`, then `e = f`.
     *
     * This justifies calling `e` <i>the</i> multiplicative identity element.
     */
    val multiplicativeIdentityUniqueness = Theorem(identityRing(G, +, *) |- ∃!(e, isNeutral(e, G, *))) {
        assume(identityRing(G, +, *))
        val existence = have(identityRing(G, +, *) |- ∃(e, isNeutral(e, G, *))) by Tautology.from(identityRing.definition, identityExistence.definition)

        val uniqueness = have((isNeutral(e, G, *), isNeutral(f, G, *)) |- (e === f)) subproof {
            val membership = have(isNeutral(e, G, *) |- e ∈ G) by Tautology.from(isNeutral.definition)
            assume(isNeutral(e, G, *))
            assume(isNeutral(f, G, *))

            // 1. e * f = f
            have(∀(x, x ∈ G ==> ((op(e, *, x) === x) /\ (op(x, *, e) === x)))) by Tautology.from(isNeutral.definition)
            thenHave(f ∈ G ==> ((op(e, *, f) === f) /\ (op(f, *, e) === f))) by InstantiateForall(f)
            val neutrality = thenHave(f ∈ G |- ((op(e, *, f) === f) /\ (op(f, *, e) === f))) by Restate
            have((op(e, *, f) === f) /\ (op(f, *, e) === f)) by Cut(membership of (e -> f), neutrality)
            val firstEq = thenHave(op(e, *, f) === f) by Tautology

            // 2. e * f = e
            have((op(f, *, e) === e) /\ (op(e, *, f) === e)) by Cut(membership of (e -> e), neutrality of (e -> f, f -> e))
            val secondEq = thenHave(e === op(e, *, f)) by Tautology

            // 3. Conclude by transitivity
            have(thesis) by Tautology.from(firstEq, secondEq, equalityTransitivity of (x -> e, y -> op(e, *, f), z -> f))
        }
        have(thesis) by ExistenceAndUniqueness(isNeutral(e, G, *))(existence, uniqueness)    
    }

    //
    // 2. Subrings
    //

    // By convention, this will always refer to the restricted operations.
    private val ★ = restrictedFunction(+, cartesianProduct(H, H))
    private val ♦ = restrictedFunction(*, cartesianProduct(H, H))

    /**
     * Subring --- `H` is a subring of `(G, +, *)` if `H` is a subset of `G`, such that `(H, +_H, *_H)` is a ring.
     *
     * We denote `H <= G` for `H` a subring of `G`.
     */
    val subring = DEF(H, G, +, *) --> ring(G, +, *) /\ subset(H, G) /\ ring(H, restrictedFunction(+, cartesianProduct(H, H)), restrictedFunction(*, cartesianProduct(H, H)))
    
    private val closedByInverse = DEF(G, *) --> ∀(x, x ∈ G ==> (inverse(x, G, *) ∈ G))
    private val neutralIncluded = ∀(e, isNeutral(e, G, *) ==> e ∈ H)
    /**
     * Another definition for a subring, when we have the identity element
     * Subring --- `H` is a subring of `(G, +, *)` if `H` is closed under '*' and '+', and closed under additing inverse
     * i.e. 'x ∈ H implies x^(-1) ∈ H'. Lastly, the multiplicative identity element is also in 'H'.
     * 
     *  We still denote `H <= G` for `H` a subring of `G`.
     */
    val identitySubring = DEF(H, G, +, *) --> identityRing(G, +, *) /\ neutralIncluded /\ closure(G, restrictedFunction(*, cartesianProduct(H, H))) /\ closure(G, restrictedFunction(+, cartesianProduct(H, H))) /\ closedByInverse(H, restrictedFunction(*, cartesianProduct(H, H)))
    
    private val allUnitsIncluded = ∀(x, (x ∈ G) /\ ∃(y, isInverse(y, x, G, *)) ==> (x ∈ U))
    /**
     * Group of units --- 'U' is the group of units of '(G, +, *)' if all the invertible elements under '*' of 'G' are in 'U',
     * and 'U' is a group under the operator '*'.
     */
    val unitGroup = DEF(U, G, +, *) --> ring(G, +, *) /\ group(U, restrictedFunction(*, cartesianProduct(U, U))) /\ allUnitsIncluded /\ subset(U, G)


    //
    // 3. Ring Homomorphism
    //

    // Extra group composition law
    private val -+ = variable
    private val -* = variable

    /**
     * Definition --- A ring homomorphism is a mapping `f: G -> H` from structures '(G, +, *)' and '(H, -+, -*)' equipped with binary operations `+`, '*', '-+' and `-*` respectively,
     * such that for all `x, y ∈ G`, we have `f(x * y) = f(x) -* f(y)` and 'f(x + y) = f(x) -+ f(y)'.
     *
     */
    val ringHomomorphism = DEF(f, G, +, *, H, -+, -*) --> ring(G, +, *) /\ ring(H, -+, -*) /\ functionFrom(f, G, H) /\ ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y))))) /\ ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y)))))

}
