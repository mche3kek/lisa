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
import lisa.fol.Common

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
     * Definition of the -x in a ring.
     * '-x' is the additive inverse of 'x' in 'G'
     */
    inline def minus(x: Term) = inverse(x, G, +)
    
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
    val ring = DEF(G, +, *) --> group(G, +) /\ abelianGroup(G, +) /\ binaryOperation(G, *) /\ closure(G, *) /\ associativityAxiom(G, *) /\ distributivityAxiom(G, +, *)
    
    /**
     * Lemma --- If `x, y ∈ G`, then `x * y ∈ G`.
     */
    val ringIsClosedByProduct = Lemma( (ring(G, +, *), x ∈ G, y ∈ G) |- op(x, *, y) ∈ G) {
        assume(ring(G, +, *))
        have(∀(x, ∀(y, (x ∈ G /\ y ∈ G) ==> (op(x, *, y) ∈ G)))) by Tautology.from(ring.definition, closure.definition)
        thenHave(∀(y, (x ∈ G /\ y ∈ G) ==> (op(x, *, y) ∈ G))) by InstantiateForall(x)
        thenHave((x ∈ G /\ y ∈ G) ==> (op(x, *, y) ∈ G)) by InstantiateForall(y)
        thenHave(thesis) by Restate
    }

    /*
     * Ring operation is functional -- The ring operations `* and +` are functional.
     */
    val ringOperationIsFunctional = Lemma(ring(G, +, *) |- (functional(*) /\ functional(+))) {
        assume(ring(G, +, *))
        val eq1 = have(ring(G, +, *) |- functional(+)) by Tautology.from(ring.definition, groupOperationIsFunctional of (* -> +))
        val eq2 = have(ring(G, +, *) |- functional(*)) by Tautology.from(ring.definition, binaryOperation.definition, functionFromImpliesFunctional of (f -> *, x -> cartesianProduct(G, G), y -> G))
        have(thesis) by Tautology.from(eq1, eq2)
    }

    /**
   * Group operation domain -- The domain of a group law is the cartesian product of the group `G` with itself.
   *
   * Follows directly from the definition of `binaryRelation`.
   */
    val ringOperationDomain = Lemma(ring(G, +, *) |- ( (relationDomain(+) === cartesianProduct(G, G)) /\ (relationDomain(*) === cartesianProduct(G, G)))) {
        assume(ring(G, +, *))
        val eq1 = have(ring(G, +, *) |- relationDomain(+) === cartesianProduct(G, G)) by Tautology.from(ring.definition,groupOperationDomain of (* -> +))
        val eq2 = have(ring(G, +, *) |- relationDomain(*) === cartesianProduct(G, G)) by Tautology.from(ring.definition, binaryOperation.definition, functionFromImpliesDomainEq of (f -> *, x -> cartesianProduct(G, G), y -> G))
        have(thesis) by Tautology.from(eq1, eq2)
    }

    /**
     * Lemma --- For elements `x, y, z` in a ring `(G, +, *)`, we have `x(y+z) = xy + xz and (x+y)z = xz + yz`.
     *
     * Practical reformulation of the [[distributivityAxiom]].
     */
    val distributivity = Lemma((ring(G, +, *), x ∈ G, y ∈ G, z ∈ G) |- ((op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z))))) {
        assume(ring(G, +, *))
        have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z)))))))) by Tautology.from(ring.definition, distributivityAxiom.definition)
        thenHave(x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z))))))) by InstantiateForall(x)
        thenHave(x ∈ G |- ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z))))))) by Restate
        thenHave(x ∈ G |- y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z)))))) by InstantiateForall(y)
        thenHave((x ∈ G, y ∈ G) |- ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z)))))) by Restate
        thenHave((x ∈ G, y ∈ G) |- z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z))))) by InstantiateForall(z)
        thenHave((x ∈ G, y ∈ G, z ∈ G) |- ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z))))) by Restate
    }

    /**
     * Theorem --- The neutral element of the binary operator '+', denoted as '0', in the structure '(G, +, *)' is an absorbing element, 
     * i.e. '0 * x = x * 0 = 0' for all 'x' in 'G'.
     */
    val absorbingElementZero = Theorem( (ring(G, +, *), x ∈ G) |- (op(x, *, identity(G,+)) === identity(G,+)) /\ (op(identity(G,+), *, x) === identity(G,+))){
        assume(ring(G, +, *))
        assume(x ∈ G)
        
        val e = identity(G, +)
        val groupG = have(group(G, +)) by Tautology.from(ring.definition)
        val eInGroup = have(e ∈ G) by Tautology.from(lastStep, identityInGroup of (* -> +))
        val x0inG = have(op(x,*,e) ∈ G) by Tautology.from(eInGroup, ringIsClosedByProduct of (y -> e))
        val zeroXinG = have(op(e,*,x) ∈ G) by Tautology.from(eInGroup, ringIsClosedByProduct of (x -> e, y -> x)) 
        val sumIDisID = have(op(e,+,e) === e) by Tautology.from(groupG, eInGroup, identityNeutrality of (* -> +, x -> e))

        // 1. x(0 + 0) = x0 + x0 <-> x0 = x0 + x0
        have((op(x,*,op(e,+,e)) === op(op(x,*,e),+,op(x,*,e))) /\ (op(op(x,+,e),*,e) === op(op(x,*,e),+,op(e,*,e)))) by Tautology.from(eInGroup, distributivity of (x -> x, y -> e, z -> e))
        val eq1 = thenHave(op(x,*,op(e,+,e)) === op(op(x,*,e),+,op(x,*,e))) by Weakening

        // this line of the proof doesn't work
        val TODO1 = have((op(e,+,e) === e) |- (op(x, *, op(e,+,e)) === op(x, *, e))) subproof {
            sorry
        }
        //thenHave( (op(e,+,e) === e) |- (op(x, *, op(e,+,e)) === op(x, *, e))) by RightSubstEq.withParametersSimple(
          //   List((op(e,+,e), e)),
            // lambda(z, op(x, *, op(e,+,e)) === op(x, *, z))
        //) 
        have(op(x, *, e) === op(x, *, op(e,+,e))) by Tautology.from(sumIDisID, TODO1)
        // 2. x0 = x0 + x0
        val final_eq1 = have(op(x,*,e) === op(op(x,*,e),+,op(x,*,e))) by Tautology.from(lastStep, eq1, equalityTransitivity of (x -> op(x,*,e), y -> op(x,*,op(e,+,e)), z -> op(op(x,*,e),+,op(x,*,e))))

        // 3. x0 + 0 = x0 + x0, so by leftCancellation 0 = x0
        have(op(op(x,*,e), +, e) === op(x, *, e)) by Tautology.from(groupG, x0inG, identityNeutrality of (* -> +, x -> op(x,*,e)))
        have(op(op(x,*,e),+,e) === op(op(x,*,e),+,op(x,*,e))) by Tautology.from(lastStep, final_eq1, equalityTransitivity of (x -> op(op(x,*,e),+,e), y -> op(x,*,e), z -> op(op(x,*,e),+,op(x,*,e))))
        
        val firstEquality = have(e === op(x,*,e)) by Tautology.from(lastStep, x0inG, eInGroup, groupG, leftCancellation of (* -> +, x -> op(x,*,e), y -> e, z -> op(x,*,e)))
            
        // 4. We have to show the other direction : 0x = 0 : (0 + 0)x = 0x + 0x        
        have((op(e,*,op(e,+,x)) === op(op(e,*,e),+,op(e,*,x))) /\ (op(op(e,+,e),*,x) === op(op(e,*,x),+,op(e,*,x)))) by Tautology.from(eInGroup, distributivity of (x -> e, y -> e, z -> x))
        val eq2 = thenHave((op(op(e,+,e), *, x) === op(op(e,*,x),+,op(e,*,x)))) by Weakening
        
        // this line of the proof doesn't work
        val TODO2 = have((op(e,+,e) === e) |- (op(op(e,+,e), *, x) === op(e, *, x))) subproof {
            sorry
        }
        // have( (op(e,+,e) === e) |- (op(op(e,+,e), *, x) === op(e, *, x))) by RightSubstEq.withParametersSimple(
        //     List((op(e,+,e), e)),
        //     lambda(z, op(x, *, z) === op(x, *, e))
        // )(sumIDisID) 
        have(op(e, *, x) === op(op(e,+,e), *, x)) by Tautology.from(TODO2, sumIDisID)
        val final_eq2 = have(op(e,*,x) === op(op(e,*,x),+,op(e,*,x))) by Tautology.from(eq2, lastStep, equalityTransitivity of (x -> op(e,*,x), y -> op(op(e,+,e), *, x), z -> op(op(e,*,x),+,op(e,*,x))))

        have(op(op(e,*,x), +, e) === op(e, *, x)) by Tautology.from(groupG, zeroXinG, identityNeutrality of (* -> +, x -> op(e,*,x)))
        have(op(op(e,*,x),+,e) === op(op(e,*,x),+,op(e,*,x))) by Tautology.from(lastStep, final_eq2, equalityTransitivity of (x -> op(op(e,*,x),+,e), y -> op(e, *, x), z -> op(op(e,*,x),+,op(e,*,x))))
        val secondEquality = have(e === op(e,*,x)) by Tautology.from(lastStep, groupG, zeroXinG, eInGroup, leftCancellation of (* -> +, x -> op(e,*,x), y -> e, z -> op(e,*,x)))
        
        // 4. We group the 2 results together with Tautology
        have(thesis) by Tautology.from(firstEquality, secondEquality)
    }
            

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
    val additiveInverseInRing = Lemma((ring(G, +, *), x ∈ G) |- inverse(x, G, +) ∈ G){
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
     * Lemma --- For any element `x` in a ring `(G, +, *)`, we have `x * e = e * x = x`.
     *
     * Practical reformulation of [[identityIsNeutral]].
     */
    val multiplicativeIdentityNeutrality = Lemma(
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
    val multiplicativeIdentityIdempotence = Theorem((identityRing(G, +, *)) |- (op(multiplicativeIdentity(G, +, *), *, multiplicativeIdentity(G, +, *)) === multiplicativeIdentity(G, +, *))) {
        assume(identityRing(G, +, *))
        val eInSet = have(multiplicativeIdentity(G, +, *) ∈ G) by Tautology.from(identityInRing)
        have(x ∈ G |- ((op(multiplicativeIdentity(G, +, *), *, x) === x) /\ (op(x, *, multiplicativeIdentity(G, +, *)) === x))) by Tautology.from(multiplicativeIdentityNeutrality)
        thenHave(x ∈ G |- op(multiplicativeIdentity(G, +, *), *, x) === x) by Weakening
        have(thesis) by Tautology.from(lastStep of (x -> multiplicativeIdentity(G, +, *)), eInSet)
    }
    

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
    val ringHomomorphismApplication = Lemma((ringHomomorphism(f, G, +, *, H, -+, -*), x ∈ G, y ∈ G) |- ((app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y))) /\ (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y))))) {
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
    val imageInCodomain = Lemma((ringHomomorphism(f, G, +, *, H, -+, -*), z ∈ G) |- app(f, z) ∈ H ){ 
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
     * Theorem --- If `f` is a ring homomorphism between `G` and `H`, then `f(1_G) = 1_H`.
     * Where 1_G and 1_H are the multiplicative identity elements
     */
    val ringHomomorphismMapsIdentityToIdentity = Theorem(
        (ringHomomorphism(f, G, +, *, H, -+, -*), identityRing(G, +, *), identityRing(H, -+, -*)) |- app(f, identity(G, *)) === identity(H, -*)
    ){
        sorry 
        /**
        assume(ringHomomorphism(f, G, +, *, H, -+, -*))
        assume(identityRing(G, +, *))
        assume(identityRing(H, -+, -*))
        val e = multiplicativeIdentity(G, +, *)
        
        // 0. e * e = e (to apply substitution)
        val eq0 = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- op(e, *, e) === e) by Tautology.from(multiplicativeIdentityIdempotence)
        
        // 1. f(e * e) = f(e) 
        have(app(f, e) === app(f, e)) by RightRefl
        thenHave(op(e, *, e) === e |- app(f, op(e, *, e)) === app(f, e)) by RightSubstEq.withParametersSimple(
           List((op(e, *, e), e)),
           lambda(z, app(f, z) === app(f, e))
        )
        val eq1 = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- app(f, op(e, *, e)) === app(f, e)) by Cut(eq0, lastStep)

        // 2. f(e * e) = f(e) ** f(e)
        val eq2 = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- app(f, op(e, *, e)) === op(app(f, e), -*, app(f, e))) by Tautology.from(
            identityInRing,
            ringHomomorphismApplication of (x -> e, y -> e)
        )

        // 3. f(e) ** f(e) = f(e)
        val eq3 = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- op(app(f, e), -*, app(f, e)) === app(f, e)) by Tautology.from(eq1, eq2, equalityTransitivity of (x -> op(app(f, e), -*, app(f, e)), y -> app(f, op(e, *, e)), z -> app(f, e)))

        // Conclude by idempotence
        */
    }
    
    
}
