package lisa.maths.algebra

import lisa.maths.algebra.GroupTheory.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.functions.FunctionProperties.*
import lisa.maths.settheory.functions.Functionals.* 
import lisa.maths.Quantifiers.*
import lisa.automation.kernel.CommonTactics.Definition
import lisa.automation.kernel.CommonTactics.ExistenceAndUniqueness
import lisa.kernel.fol.FOL.VariableLabel
import lisa.automation.settheory.SetTheoryTactics.TheConditional

object RingTheory extends lisa.Main {
    // Operations
    private val + = variable
    private val * = variable
    private val - = variable

    // Ring elements
    private val x, y, z, t = variable

    // Identity elements
    private val e, f = variable

    // Sets in the ring 
    private val G, H, U = variable

    /**
     * Short-hand alias for `x operator y`.
     * In ring context we have x*y or x+y
     */
    inline def op(x: Term, operator : Term, y: Term) = app(operator, pair(x, y))
    
    /**
     * Definition of the substraction in a ring.
     * for all 'x, y' in 'G', 'x - y = x + (-y)', where '-y' is the additive inverse of 'y' in 'G'
     */
    inline def substract(G: Term, x: Term, operatorMinus: Term, y: Term, operatorPlus: Term) = app(operatorPlus, pair(x, inverse(y, G, operatorPlus)))
    
    //
    // 1. Basic definitions and results
    //

    /**
     * Closure --- 'G' is closed under the binary operator '*' if and only if, for all 'x, y' in 'G',
     * we have 'x * y' in 'G'.
     */
    val closure = DEF(G, *) --> ∀(x, ∀(y, (x ∈ G /\ y ∈ G) ==> (op(x, *, y) ∈ G)))
    
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
    val ring = DEF(G, +, *) --> group(G, +) /\ abelianGroup(G, +) /\ closure(G, *) /\ associativityAxiom(G, *) /\ distributivityAxiom(G, *, +)
    
    // The neutral element of the binary operator '+', denoted as '0', in the structure '(G, +, *)' is an absorbing element, 
    // i.e. '0 * x = x * 0 = 0' for all 'x' in 'G'.
    val absorbingElementZero = (ring(G,+,*) /\ isNeutral(e, G, +)) ==> ∀(x, x ∈ G ==> (op(x, *, e) === e) /\ (op(e, *, x) === e))

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
        have(thesis) by Tautology.from(ring.definition, identityUniqueness of (G -> G, * -> +))
    }

    /**
     * Theorem --- The additive inverse of an element `x` (i.e. `y` such that `x + y = y + x = e`) in `G` is unique.
     */
    val additiveInverseUniqueness = Theorem((ring(G, +, *), x ∈ G) |- ∃!(y, isInverse(y, x, G, +)) ){
        assume(ring(G, +, *))
        have(thesis) by Tautology.from(ring.definition, inverseUniqueness of (G -> G, * -> +))
    }

    /**
     * Lemma --- The additive inverse element `y` of `x` is in `G`.
     */
    val additiveInverseInRing = Lemma(
        (ring(G, +, *), x ∈ G) |- inverse(x, G, +) ∈ G
    ) {
        assume(ring(G, +, *))
        have(group(G, +)) by Tautology.from(ring.definition)
        have(thesis) by Tautology.from(inverseInGroup of (G -> G, * -> +), lastStep)
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
            thenHave(e === op(e, *, f)) by Tautology

            // 3. Conclude by transitivity
            have(thesis) by Tautology.from(firstEq, lastStep, equalityTransitivity of (x -> e, y -> op(e, *, f), z -> f))
        }
        have(thesis) by ExistenceAndUniqueness(isNeutral(e, G, *))(existence, uniqueness)    
    }

    /**
     * Defines the multiplicative identity element of `(G, +, *)`.
     */
    val multiplicativeIdentity = DEF(G, +, *) --> TheConditional(e, isNeutral(e, G, *))(multiplicativeIdentityUniqueness)

    /**
     * Lemma --- The identity element is neutral by definition.
     */
    private val identityIsNeutral = Lemma(identityRing(G, +, *) |- isNeutral(multiplicativeIdentity(G, +, *), G, *)) {
        sorry
        // have(isNeutral(multiplicativeIdentity(G, +, *), G, *)) by Definition(multiplicativeIdentity, multiplicativeIdentityUniqueness)(G, +, *)
    }

    /**
     * Lemma --- For any element `x` in a group `(G, *)`, we have `x * e = e * x = x`.
     *
     * Practical reformulation of [[identityIsNeutral]].
     */
    val identityNeutrality = Lemma(
        (identityRing(G, +, *), x ∈ G) |- (op(multiplicativeIdentity(G, +, *), *, x) === x) /\ (op(x, *, multiplicativeIdentity(G, +, *)) === x)
    ) {
        have(identityRing(G, +, *) |- ∀(x, (x ∈ G) ==> ((op(multiplicativeIdentity(G, +, *), *, x) === x) /\ (op(x, *, multiplicativeIdentity(G, +, *)) === x)))) by Tautology.from(
            identityIsNeutral,
            isNeutral.definition of (e -> multiplicativeIdentity(G, +, *))
        )
        thenHave(identityRing(G, +, *) |- (x ∈ G) ==> ((op(multiplicativeIdentity(G, +, *), *, x) === x) /\ (op(x, *, multiplicativeIdentity(G, +, *)) === x))) by InstantiateForall(x)
        thenHave(thesis) by Restate
    }

    /**
     * Theorem --- The identity element of an identity ring belongs to the ring.
     */
    val identityInRing = Theorem(identityRing(G, +, *) |- (multiplicativeIdentity(G, +, *) ∈ G)){
        have(thesis) by Tautology.from(identityIsNeutral, isNeutral.definition of (e -> multiplicativeIdentity(G, +, *)))
    }
    
    /**
     * Theorem --- The multiplicative identity `e` of a ring `(G, +, *)` is idempotent, i.e. `e * e = e'.
     */
    /**
    val multiplicativeIdentityIdempotence = Theorem((identityRing(G, +, *)) |- (op(multiplicativeIdentity(G, +, *), *, multiplicativeIdentity(G, +, *)) === multiplicativeIdentity(G, +, *))) {
        assume(identityRing(G, +, *))
        assume(x∈G)
        assume(multiplicativeIdentity(G, +, *) ∈ G)
        have((op(multiplicativeIdentity(G, +, *), *, x) === x) /\ (op(x, *, multiplicativeIdentity(G, +, *)) === x)) by Tautology.from(identityNeutrality)
        val test = thenHave(op(multiplicativeIdentity(G, +, *), *, x) === x) by Weakening
       
        have(thesis) by Tautology.from(test of (x -> multiplicativeIdentity(G, +, *)))
    }
    */

    /**
     * Theorem --- In a ring '(G, +, *)', we have 'y + x = z + x ==> y = z'.
     */
    val CancellationLaw = Theorem((ring(G, +, *), x ∈ G, y ∈ G, z ∈ G) |- (op(y, +, x) === op(z, +, x)) ==> (y === z)){
        have(thesis) by Tautology.from(ring.definition, rightCancellation of (G -> G, * -> +))
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

    // If 'x' is in 'G' and is invertible, then its inverse is also in 'G'
    private val closedByInverse = DEF(G, *) --> ∀(x, x ∈ G ==> (inverse(x, G, *) ∈ G))

    // If the set 'G' has an identity element under the binary operator '*', then this element is in the subset 'H'
    // It is used to define a subring in another way than the previous definition
    private val neutralIncluded = ∃(e, isNeutral(e, G, *) ==> e ∈ H)

    /**
     * Another definition for a subring, when we have the identity element
     * Subring --- `H` is a subring of `(G, +, *)` if `H` is closed under '*' and '+', and closed under additing inverse
     * i.e. 'x ∈ H implies x^(-1) ∈ H'. Lastly, the multiplicative identity element is also in 'H'.
     * 
     *  We still denote `H <= G` for `H` a subring of `G`.
     */
    val identitySubring = DEF(H, G, +, *) --> identityRing(G, +, *) /\ neutralIncluded /\ closure(H, restrictedFunction(*, cartesianProduct(H, H))) /\ closure(H, restrictedFunction(+, cartesianProduct(H, H))) /\ closedByInverse(H, restrictedFunction(*, cartesianProduct(H, H)))
    
    //
    // 3. Group of units
    //

    // By convention, this will always refer to the restricted operations on the group of units 'U'.
    private val opU = restrictedFunction(*, cartesianProduct(U, U))
    
    // if an element has an inverse under '*' in 'G', then it is in the group of units 'U'
    private val allUnitsIncluded = DEF(U, G, *) --> ∀(x, (x ∈ G) /\ ∃(y, isInverse(y, x, G, *)) ==> (x ∈ U))

    /**
     * Group of units --- 'U' is the group of units of '(G, +, *)' if all the invertible elements under '*' of 'G' are in 'U',
     * and 'U' is a group under the operator '*'.
     */
    val unitGroup = DEF(U, G, +, *) --> ring(G, +, *) /\ group(U, opU) /\ allUnitsIncluded(U, G, *) /\ subset(U, G)

    /**
     * Lemma --- If an element is in the group of units, then it has an inverse under the binary operation '*' restricted to 'U'
     */
    val hasInverse = Lemma( (unitGroup(U, G, +, *), x ∈ U) |- ∃(y, isInverse(y, x, U, opU))){
        assume(unitGroup(U, G, +, *))
        val UisGroup = have(group(U, opU)) by Tautology.from(unitGroup.definition)
        val statement1 = have(group(U, opU) |- ∀(x, x ∈ U ==> ∃(y, isInverse(y, x, U, opU)))) by Tautology.from(UisGroup, group.definition of(G -> U, * -> opU), inverseExistence.definition of(G -> U, * -> opU))
        have(unitGroup(U, G, +, *) |- ∀(x, x ∈ U ==> ∃(y, isInverse(y, x, U, opU)))) by Tautology.from(statement1, unitGroup.definition)
        thenHave(unitGroup(U, G, +, *) |- (x ∈ U ==> ∃(y, isInverse(y, x, U, opU)))) by InstantiateForall(x)
        thenHave(thesis) by Restate
    }

    /**
     * Theorem --- The inverse of an element `x` (i.e. `y` such that `x * y = y * x = e`) in the gropu of unit `U` is unique.
     */

    val hasInverseUniqueness = Theorem((unitGroup(U, G, +, *), x ∈ U) |- ∃!(y, isInverse(y, x, U, opU))){
        assume(unitGroup(U, G, +, *))
        have(group(U, opU)) by Tautology.from(unitGroup.definition)
        have(thesis) by Tautology.from(lastStep, inverseUniqueness of (G -> U, * -> opU))
    }

    /**
     * Lemma --- If an element in the structure '(G, +, *)' has an inverse, then it is in the group of units 'U'
     */
    val inverseInUnitGroup = Lemma(unitGroup(U, G, +, *) |- ((x ∈ G /\ ∃(y, isInverse(y, x, G, *))) ==> x ∈ U)){
        assume(unitGroup(U, G, +, *))
        have(unitGroup(U, G, +, *) |- ∀(x, (x ∈ G) /\ ∃(y, isInverse(y, x, G, *)) ==> (x ∈ U))) by Tautology.from(unitGroup.definition, allUnitsIncluded.definition)
        thenHave(thesis) by InstantiateForall(x)
    }


    //
    // 4. Ring Homomorphism
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
    
    /**
   * Lemma --- Practical reformulation of the homomorphism definition.
   */
    val ringHomomorphismApplication = Lemma(
        (ringHomomorphism(f, G, +, *, H, -+, -*), x ∈ G, y ∈ G) |- ((app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y))) /\ (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y))))
    ) {
    assume(ringHomomorphism(f, G, +, *, H, -+, -*))
    val init = have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y))))) /\ ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y)))))) by Tautology.from(ringHomomorphism.definition)
    thenHave(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y)))))) by Weakening
    thenHave((x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y)))))) by InstantiateForall(x)
    thenHave((x ∈ G) |- ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y))))) by Restate
    val eq1 = thenHave((x ∈ G) |- y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y)))) by InstantiateForall(y)
    
    have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y)))))) by Weakening(init)
    thenHave((x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y)))))) by InstantiateForall(x)
    thenHave((x ∈ G) |- ∀(y, y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y))))) by Restate
    thenHave((x ∈ G) |- y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y)))) by InstantiateForall(y)

    have(thesis) by Tautology.from(eq1, lastStep)
    }


    /**
     * Lemma --- If `f` is a ring homomorphism, then `f(x) ∈ H` for all `x ∈ G`.
     */
    private val imageInCodomain = Lemma((ringHomomorphism(f, G, +, *, H, -+, -*), z ∈ G) |- app(f, z) ∈ H ){ 
        have(ringHomomorphism(f, G, +, *, H, -+, -*) |- functionFrom(f, G, H)) by Tautology.from(ringHomomorphism.definition)
        have(thesis) by Tautology.from(lastStep, functionAppInCodomain of (x -> G, y -> H, t -> z)) 
     }
        
    
    /**
     * Theorem --- If `f` is a ring homomorphism between `G` and `H`, then `f(0_G) = 0_H`.
     * Where 0_G and 0_H are the additive identity elements
     */
    val ringHomomorphismMapsZeroToZero = Theorem((ringHomomorphism(f, G, +, *, H, -+, -*)) |- (app(f, identity(G,+)) === identity(H, -+))){
        assume(ringHomomorphism(f, G, +, *, H, -+, -*))

        val e = identity(G, +)

        val groupG = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- group(G, +)) by Tautology.from(ringHomomorphism.definition, ring.definition)
        val groupH = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- group(H, -+)) by Tautology.from(ringHomomorphism.definition, ring.definition of (G -> H, this.+ -> -+, * -> -*))

        val identityInG = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- e ∈ G) by Cut(groupG, identityInGroup of (* -> +))
        val appInH = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- app(f, e) ∈ H) by Cut(identityInG, imageInCodomain of (z -> e))

        // 0. e * e = e (to apply substitution)
        have(group(G, +) |- op(e, +, e) === e) by Tautology.from(
           identityInGroup of (* -> +),
           identityIdempotence of (* -> +, x -> e)
        )
        val eq0 = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- op(e, +, e) === e) by Cut(groupG, lastStep)

        // 1. f(e * e) = f(e)
        have(app(f, e) === app(f, e)) by Restate
        thenHave(op(e, +, e) === e |- app(f, op(e, +, e)) === app(f, e)) by RightSubstEq.withParametersSimple(
            List((op(e, +, e), e)),
            lambda(z, app(f, z) === app(f, e))
        )
        have(ringHomomorphism(f, G, +, *, H, -+, -*) |- app(f, op(e, +, e)) === app(f, e)) by Cut(eq0, lastStep)
        val eq1 = thenHave(ringHomomorphism(f, G, +, *, H, -+, -*) |- app(f, e) === app(f, op(e, +, e))) by Restate
        // 2. f(e * e) = f(e) ** f(e)
        val eq2 = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- app(f, op(e, +, e)) === op(app(f, e), -+, app(f, e))) by Tautology.from(
            identityInG,
            ringHomomorphismApplication of (x -> e, y -> e)
        )

        // 3. f(e) ** f(e) = f(e)
        val eq3 = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- op(app(f, e), -+, app(f, e)) === app(f, e)) by Tautology.from(eq1, eq2, equalityTransitivity of (x -> app(f, e), y -> app(f, op(e, +, e)), z -> op(app(f, e), -+, app(f, e))))

        // Conclude by idempotence
        have((ringHomomorphism(f, G, +, *, H, -+, -*), app(f, e) ∈ H) |- (op(app(f, e), -+, app(f, e)) === app(f, e)) <=> (app(f, e) === identity(H, -+))) by Cut(
            groupH,
            identityIdempotence of (x -> app(f, e), G -> H, * -> -+)
        )
        have(ringHomomorphism(f, G, +, *, H, -+, -*) |- (op(app(f, e), -+, app(f, e)) === app(f, e)) <=> (app(f, e) === identity(H, -+))) by Cut(
            appInH,
            lastStep
        )
        have(thesis) by Tautology.from(lastStep, eq3)
    }
    /**
     * Theorem --- If `f` is a ring homomorphism between `G` and `H`, then `f(e_G) = e_H`.
     */
    /**
    val ringHomomorphismMapsIdentityToIdentity = Theorem(
        (ringHomomorphism(f, G, +, *, H, -+, -*), identityRing(G, +, *), identityRing(H, -+, -*)) |- app(f, identity(G, *)) === identity(H, -*)
    ){
        assume(ringHomomorphism(f, G, +, *, H, -+, -*))
        assume(identityRing(G, +, *))
        assume(identityRing(H, -+, -*))
        val e = multiplicativeIdentity(G, +, *)
        
        // 0. e * e = e (to apply substitution)
        have(op(e, *, e) === e) by Tautology.from(isNeutral.definition)

        // 1. f(e * e) = f(e) 

        // 2. f(e * e) = f(e) ** f(e)

        // 3. f(e) ** f(e) = f(e)

        // Conclude by idempotence
    }
    */
    
}
