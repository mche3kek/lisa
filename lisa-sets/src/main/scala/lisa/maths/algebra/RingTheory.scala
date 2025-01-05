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
import lisa.automation.Congruence.*
import lisa.automation.Congruence

object RingTheory extends lisa.Main {
    // Operations
    private val + = variable
    private val * = variable

    // Formula
    private val p1 = formulaVariable
    private val p2 = formulaVariable
    private val p3 = formulaVariable

    // Ring elements
    private val x, y, z, t = variable

    // Identity elements
    private val e, f = variable

    // Sets in the ring 
    private val G, H, U = variable
    
    /**
     * Short-hand alias for `x operator y`.
     * In ring context we have x*y or x+y.
     */
    inline def op(x: Term, operator : Term, y: Term) = app(operator, pair(x, y))
    
    /**
     * Definition of '-x' in a ring.
     * '-x' is the additive inverse of 'x' in 'G'.
     */
    inline def minus(x: Term) = inverse(x, G, +)
    
    //
    // 1. Basic definitions and results
    //

    /**
     * Closure --- 'G' is closed under the binary operator '*' if and only if, for all 'x, y' in 'G', we have 'x * y' in 'G'.
     */
    private val closure = DEF(G, *) --> ∀(x, ∀(y, (x ∈ G /\ y ∈ G) ==> (op(x, *, y) ∈ G)))
    
    /**
     * Distributivity --- `*, +` are distributive in `G`, if `x * (y + z) = x * y + x * z'
     * and '(x + y) * z = x * z + y * z ` for all `x, y, z` in `G`.
     */
    private val distributivityAxiom = DEF(G, +, *) --> ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z)))))))

    /**
     * Ring --- A ring (G, +, *) is a set along with a law of composition `*` and '+', satisfying [[abelianGroup]], [[closure]],
     * [[associativityAxiom]], [[identityExistence]] and [[distributivityAxiom]].
     */
    val ring = DEF(G, +, *) --> abelianGroup(G, +) /\ binaryOperation(G, *) /\ closure(G, *) /\ associativityAxiom(G, *) /\ distributivityAxiom(G, +, *)
    //group(G, +) /\ 

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
     * No Zero Divisors --- A ring has no zero divisors if 'x * y = 0 ==> x = 0 or y = 0' for all 'x, y' in 'G'.
     * '0' denotes the identity element under the '+' operation.
     */
    private val noZeroDivisorsAxiom = DEF(G, +, *) --> ring(G, +, *) /\ ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> ( op(x, *, y) === identity(G, +) ==> ((x === identity(G, +)) \/ (y === identity(G, +))))))
    
    /**
     * Integral Domain --- A ring is said to be an integral domain if it is commutative, that an identity element under '*' exists, and that it has no zero divisors.
     * i.e. it satisfies [[commutativeRing]], [[identityRing]] and [[noZeroDivisorsAxiom]].
     */
    val integralDomain = DEF(G, +, *) --> ring(G, +, *) /\ commutativeRing(G, +, *) /\ identityRing(G, +, *) /\ noZeroDivisorsAxiom(G, +, *)

    /**
     * Lemma --- If `x, y ∈ G`, then `x * y ∈ G`.
     * 
     * Practical reformulation of the [[closure]].
     */
    val ringIsClosedByProduct = Lemma( (ring(G, +, *), x ∈ G, y ∈ G) |- op(x, *, y) ∈ G
    ) {
        assume(ring(G, +, *))
        have(∀(x, ∀(y, (x ∈ G /\ y ∈ G) ==> (op(x, *, y) ∈ G)))) by Tautology.from(ring.definition, closure.definition)
        thenHave(∀(y, (x ∈ G /\ y ∈ G) ==> (op(x, *, y) ∈ G))) by InstantiateForall(x)
        thenHave((x ∈ G /\ y ∈ G) ==> (op(x, *, y) ∈ G)) by InstantiateForall(y)
        thenHave(thesis) by Restate
    }

    /**
     * Lemma --- For elements `x, y, z` in a ring `(G, +, *)`, we have `x(y + z) = xy + xz and (x + y)z = xz + yz`.
     *
     * Practical reformulation of the [[distributivityAxiom]].
     */
    val distributivity = Lemma((ring(G, +, *), x ∈ G, y ∈ G, z ∈ G) |- ((op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z))))
    ) {
        assume(ring(G, +, *))
        have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z)))))))) by Tautology.from(ring.definition, distributivityAxiom.definition)
        thenHave(x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z))))))) by InstantiateForall(x)
        thenHave(x ∈ G |- ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z))))))) by Restate
        thenHave(x ∈ G |- y ∈ G ==> ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z)))))) by InstantiateForall(y)
        thenHave((x ∈ G, y ∈ G) |- ∀(z, z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z)))))) by Restate
        thenHave((x ∈ G, y ∈ G) |- z ∈ G ==> ( (op(x,*,op(y,+,z)) === op(op(x,*,y),+,op(x,*,z))) /\ (op(op(x,+,y),*,z) === op(op(x,*,z),+,op(y,*,z))))) by InstantiateForall(z)
        thenHave(thesis) by Restate
    }

    /**
     * Lemma --- For elements `x, y` in an commutative ring `(G, +, *)`, we have `xy = yx`.
     *
     * Practical reformulation of [[commutativityAxiom]] but for rings.
     */
    val ringCommutativity = Lemma((commutativeRing(G, +, *), x ∈ G, y ∈ G) |- op(x, *, y) === op(y, *, x)
    ) {
        assume(commutativeRing(G, +, *))
        have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (op(x, *, y) === op(y, *, x))))) by Tautology.from(commutativeRing.definition, commutativityAxiom.definition)
        thenHave(x ∈ G ==> ∀(y, y ∈ G ==> (op(x, *, y) === op(y, *, x)))) by InstantiateForall(x)
        thenHave(x ∈ G |- ∀(y, y ∈ G ==> (op(x, *, y) === op(y, *, x)))) by Restate
        thenHave(x ∈ G |- (y ∈ G ==> (op(x, *, y) === op(y, *, x)))) by InstantiateForall(y)
        thenHave((x ∈ G, y ∈ G) |- ((op(x, *, y) === op(y, *, x)))) by Restate
    }

    /**
     * Lemma ---  A ring has no zero divisors if 'x * y = 0 ==> x = 0 or y = 0' for all 'x, y' in 'G'.
     * '0' denotes the identity element under the '+' operation.
     * 
     * Practical reformulation of the [[noZeroDivisorsAxiom]].
     */
    val noZeroDivisors = Lemma((integralDomain(G, +, *), x ∈ G, y ∈ G) |- ( op(x, *, y) === identity(G, +) ==> ((x === identity(G, +)) \/ (y === identity(G, +))))
    ){
        assume(integralDomain(G, +, *))
        assume(x ∈ G)
        assume(y ∈ G)
        
        have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> ( op(x, *, y) === identity(G, +) ==> ((x === identity(G, +)) \/ (y === identity(G, +))))))) by Tautology.from(integralDomain.definition, noZeroDivisorsAxiom.definition)
        thenHave(x ∈ G ==> ∀(y, y ∈ G ==> ( op(x, *, y) === identity(G, +) ==> ((x === identity(G, +)) \/ (y === identity(G, +)))))) by InstantiateForall(x)
        thenHave(x ∈ G |- ∀(y, y ∈ G ==> ( op(x, *, y) === identity(G, +) ==> ((x === identity(G, +)) \/ (y === identity(G, +)))))) by Restate
        thenHave(x ∈ G |- y ∈ G ==> ( op(x, *, y) === identity(G, +) ==> ((x === identity(G, +)) \/ (y === identity(G, +))))) by InstantiateForall(y)
        thenHave(thesis) by Restate
    }

    /*
     * Ring operation is functional -- The ring operations `* and +` are functional.
     */
    val ringOperationIsFunctional = Lemma(ring(G, +, *) |- (functional(*) /\ functional(+))
    ) {
        assume(ring(G, +, *))
        // 1. '+' is functional
        val eq1 = have(ring(G, +, *) |- functional(+)) by Tautology.from(
            ring.definition, 
            abelianGroup.definition of (* -> +),
            groupOperationIsFunctional of (* -> +)
        )
        // 2. '*' is functional
        val eq2 = have(ring(G, +, *) |- functional(*)) by Tautology.from(
            ring.definition, 
            binaryOperation.definition, 
            functionFromImpliesFunctional of (f -> *, x -> cartesianProduct(G, G), y -> G)
        )
        have(thesis) by Tautology.from(eq1, eq2)
    }

    /**
     * Ring operation domain -- The domain of a ring law is the cartesian product of the ring `G` with itself.
     *
     * Follows directly from the definition of `binaryRelation`.
     */
    val ringOperationDomain = Lemma(ring(G, +, *) |- ( (relationDomain(+) === cartesianProduct(G, G)) /\ (relationDomain(*) === cartesianProduct(G, G)))
    ) {
        assume(ring(G, +, *))
        val eq1 = have(ring(G, +, *) |- relationDomain(+) === cartesianProduct(G, G)) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +), groupOperationDomain of (* -> +))
        val eq2 = have(ring(G, +, *) |- relationDomain(*) === cartesianProduct(G, G)) by Tautology.from(ring.definition, binaryOperation.definition, functionFromImpliesDomainEq of (f -> *, x -> cartesianProduct(G, G), y -> G))
        have(thesis) by Tautology.from(eq1, eq2)
    }

    
    /**
     * Theorem --- The neutral element of the binary operator '+', denoted as '0', in the structure '(G, +, *)' is an absorbing element, 
     * i.e. '0x = x0 = 0' for all 'x' in 'G'.
     */
    val absorbingElementZero = Theorem( (ring(G, +, *), x ∈ G) |- (op(x, *, identity(G,+)) === identity(G,+)) /\ (op(identity(G,+), *, x) === identity(G,+))
    ){
        assume(ring(G, +, *))
        assume(x ∈ G)
        
        val e = identity(G, +)
        val groupG = have(group(G, +)) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +))
        val eInGroup = have(e ∈ G) by Tautology.from(lastStep, identityInGroup of (* -> +))
        val x0inG = have(op(x,*,e) ∈ G) by Tautology.from(eInGroup, ringIsClosedByProduct of (y -> e))
        val zeroXinG = have(op(e,*,x) ∈ G) by Tautology.from(eInGroup, ringIsClosedByProduct of (x -> e, y -> x)) 
        val sumIDisID = have(op(e,+,e) === e) by Tautology.from(groupG, eInGroup, identityNeutrality of (* -> +, x -> e))

        // First equality: 0 = x0
        val firstResult = have((ring(G, +, *), x ∈ G) |- (e === op(x,*,e))) subproof {
            // 1. (x(0 + 0) = x0 + x0) <-> (x0 = x0 + x0)
            val step1 = have((op(x,*,op(e,+,e)) === op(op(x,*,e),+,op(x,*,e)))) by Tautology.from(eInGroup, distributivity of (x -> x, y -> e, z -> e))
            have((op(e,+,e) === e) |- (op(x, *, op(e,+,e)) === op(x, *, e))) by Congruence
            have(op(x, *, e) === op(x, *, op(e,+,e))) by Tautology.from(sumIDisID, lastStep)
            val eq1 = have(op(x,*,e) === op(op(x,*,e),+,op(x,*,e))) by Tautology.from(lastStep, step1, equalityTransitivity of (x -> op(x,*,e), y -> op(x,*,op(e,+,e)), z -> op(op(x,*,e),+,op(x,*,e))))

            // 2. x0 + 0 = x0 + x0, then by leftCancellation 0 = x0
            have(op(op(x,*,e), +, e) === op(x, *, e)) by Tautology.from(groupG, x0inG, identityNeutrality of (* -> +, x -> op(x,*,e)))
            have(op(op(x,*,e),+,e) === op(op(x,*,e),+,op(x,*,e))) by Tautology.from(lastStep, eq1, equalityTransitivity of (x -> op(op(x,*,e),+,e), y -> op(x,*,e), z -> op(op(x,*,e),+,op(x,*,e))))
            have(thesis) by Tautology.from(lastStep, x0inG, eInGroup, groupG, leftCancellation of (* -> +, x -> op(x,*,e), y -> e, z -> op(x,*,e)))
        }
            
        // Second equality : 0 = 0x  
        val secondResult = have((ring(G, +, *), x ∈ G) |- (e === op(e,*,x))) subproof {
            // 1. ((0 + 0)x = 0x + 0x) <-> (0x = 0x + 0x)
            val step1 = have((op(op(e,+,e),*,x) === op(op(e,*,x),+,op(e,*,x)))) by Tautology.from(eInGroup, distributivity of (x -> e, y -> e, z -> x))
            have((op(e,+,e) === e) |- (op(op(e,+,e), *, x) === op(e, *, x))) by Congruence
            have(op(e, *, x) === op(op(e,+,e), *, x)) by Tautology.from(lastStep, sumIDisID)
            val eq1 = have(op(e,*,x) === op(op(e,*,x),+,op(e,*,x))) by Tautology.from(step1, lastStep, equalityTransitivity of (x -> op(e,*,x), y -> op(op(e,+,e), *, x), z -> op(op(e,*,x),+,op(e,*,x))))
            
            // 2. 0x + 0 = 0x + 0x, then by leftCancellation 0 = 0x
            have(op(op(e,*,x), +, e) === op(e, *, x)) by Tautology.from(groupG, zeroXinG, identityNeutrality of (* -> +, x -> op(e,*,x)))
            have(op(op(e,*,x),+,e) === op(op(e,*,x),+,op(e,*,x))) by Tautology.from(lastStep, eq1, equalityTransitivity of (x -> op(op(e,*,x),+,e), y -> op(e, *, x), z -> op(op(e,*,x),+,op(e,*,x))))
            have(thesis) by Tautology.from(lastStep, groupG, zeroXinG, eInGroup, leftCancellation of (* -> +, x -> op(e,*,x), y -> e, z -> op(e,*,x)))
        }
        
        have(thesis) by Tautology.from(firstResult, secondResult)
    }
    
    /**
     * Theorem --- If 'x' is in 'G', then '-(-x) = x'.
     * Where -x denotes the inverse of x under the operation '+'.   
     */
    val additiveInverseIsInvolutive = Theorem((ring(G, +, *), x ∈ G) |- minus(minus(x)) === x
    ){
        have(thesis) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +), inverseIsInvolutive of (* -> +))
    }

    
    /**
     * Theorem --- In a ring '(G, +, *)', an additive identity element is unique, i.e. if both `e + x = x + e = x` and
     * `f + x = x + f = x` for all `x`, then `e = f`.
     */
    val additiveIdentityUniqueness = Theorem(ring(G, +, *) |- ∃!(e, isNeutral(e, G, +))
    ) {
        have(thesis) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +), identityUniqueness of (G -> G, * -> +))
    }

    /**
     * Theorem --- The additive inverse of an element `x` (i.e. `y` such that `x + y = y + x = e`) in `G` is unique.
     */
    val additiveInverseUniqueness = Theorem((ring(G, +, *), x ∈ G) |- ∃!(y, isInverse(y, x, G, +)) 
    ){
        assume(ring(G, +, *))
        have(thesis) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +), inverseUniqueness of (G -> G, * -> +))
    }

    /**
     * Lemma --- The additive inverse element `y` of `x` is in `G`.
     */
    val additiveInverseInRing = Lemma((ring(G, +, *), x ∈ G) |- inverse(x, G, +) ∈ G
    ){
        have(thesis) by Tautology.from(inverseInGroup of (G -> G, * -> +), ring.definition, abelianGroup.definition of (* -> +))
    }
 
    /**
     * Theorem --- In a ring, we have '-(xy) = x(-y)' and '-(xy) = (-x)y'. 
     * Where '-x' denotes the additive inverse of 'x'.
     *
     * It's a consequence of distributivity.
     */
    val negationDistribution = Theorem((ring(G, +, *), x ∈ G, y ∈ G) |- ((minus(op(x,*,y)) === op(x, *, minus(y))) /\ (minus(op(x,*,y)) === op(minus(x), *, y)))
    ){
        assume(ring(G, +, *))
        assume(x ∈ G)
        assume(y ∈ G)
        
        val prod1InG = have(op(x,*,y) ∈ G) by Tautology.from(ringIsClosedByProduct)
        val groupG = have(group(G, +)) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +))
        val abelianGroupG = have(abelianGroup(G, +)) by Tautology.from(ring.definition)
        
        // First equality : -(xy) = x(-y)
        val firstProof = have((ring(G, +, *), x ∈ G, y ∈ G) |- (minus(op(x,*,y)) === op(x, *, minus(y)))) subproof {
            val invInG = have(minus(y) ∈ G) by Tautology.from(additiveInverseInRing of (x -> y))
            val prod2InG = have(op(x,*,minus(y)) ∈ G) by Tautology.from(lastStep, ringIsClosedByProduct of (y -> minus(y)))
            
            // 1. (y + (-y)) = 0 ==> x(y + (-y)) = x0
            val step1 = have(op(y, +, minus(y)) === identity(G, +)) by Tautology.from(groupG, inverseCancellation of (* -> +, x -> y))
            have((op(y, +, minus(y)) === identity(G, +)) |- (op(x, *, op(y, +, minus(y))) === op(x, *, identity(G, +)))) by Congruence
            val eq1 = have(op(x, *, op(y, +, minus(y))) === op(x, *, identity(G, +))) by Tautology.from(lastStep, step1)
            
            // 2. x0 = 0, so x(y +(-y)) = 0
            have(op(x, *, identity(G, +)) === identity(G, +)) by Tautology.from(absorbingElementZero)
            val eq2 = have(op(x, *, op(y, +, minus(y))) === identity(G, +)) by Tautology.from(lastStep, eq1, equalityTransitivity of (x -> op(x, *, op(y, +, minus(y))), y -> op(x, *, identity(G, +)), z -> identity(G, +)))
            
            // 3. x(y + (-y)) = xy + x(-y), so x(-y) + xy = 0
            have(op(x, *, op(y, +, minus(y))) === (op(op(x,*,y),+,op(x,*,minus(y))))) by Tautology.from(invInG, distributivity of (z -> minus(y)))
            val step2 = have((op(op(x,*,y), +, op(x,*,minus(y)))) === identity(G, +)) by Tautology.from(lastStep, eq2, equalityTransitivity of (x -> (op(op(x,*,y),+,op(x,*,minus(y)))), y -> op(x, *, op(y, +, minus(y))), z -> identity(G, +)))
            have(op(op(x,*,minus(y)), +, op(x,*,y)) === op(op(x,*,y), +, op(x,*,minus(y)))) by Tautology.from(abelianGroupG, prod1InG, prod2InG, commutativity  of (* -> +, x -> op(x,*,minus(y)), y -> op(x,*,y)))
            val eq3 = have(op(op(x,*,minus(y)), +, op(x,*,y)) === identity(G, +)) by Tautology.from(lastStep, step2, equalityTransitivity of (x -> op(op(x,*,minus(y)), +, op(x,*,y)), y -> op(op(x,*,y), +, op(x,*,minus(y))), z -> identity(G, +)))
            
            // 4. xy = -(x(-y))
            val eq4 = have(op(x,*,y) === minus(op(x,*,minus(y)))) by Tautology.from(prod1InG, prod2InG, lastStep, groupG, inverseTest of (* -> +, x -> op(x,*,minus(y)), y -> op(x,*,y)))

            // 5. -(xy) = -(-(x(-y))), so -(xy) = x(-y) by involution
            have((op(x,*,y) === minus(op(x,*,minus(y)))) |- (minus(op(x,*,y)) === minus(minus(op(x,*,minus(y)))))) by Congruence
            val eq5 = have(minus(op(x,*,y)) === minus(minus(op(x,*,minus(y))))) by Tautology.from(lastStep, eq4)
            have(minus(minus(op(x,*,minus(y)))) === op(x,*,minus(y))) by Tautology.from(lastStep, additiveInverseIsInvolutive of (x -> op(x,*,minus(y))), prod2InG)
            have(thesis) by Tautology.from(lastStep, eq5, equalityTransitivity of (x -> minus(op(x,*,y)), y -> minus(minus(op(x,*,minus(y)))), z -> op(x,*,minus(y))))
        }

        // Second equality : -(xy) = (-x)y
        val secondProof = have((ring(G, +, *), x ∈ G, y ∈ G) |- (minus(op(x,*,y)) === op(minus(x), *, y))) subproof {
            val invInG = have(minus(x) ∈ G) by Tautology.from(additiveInverseInRing)
            val prod2InG = have(op(minus(x),*,y) ∈ G) by Tautology.from(lastStep, ringIsClosedByProduct of (x -> minus(x)))
            
            // 1. (x + (-x))y = 0y
            val step1 = have(op(x, +, minus(x)) === identity(G, +)) by Tautology.from(groupG, inverseCancellation of (* -> +))
            have((op(x, +, minus(x)) === identity(G, +)) |- (op( op(x, +, minus(x)), *, y) === op(identity(G,+), *, y))) by Congruence
            val eq1 = have(op(op(x, +, minus(x)), *, y) === op(identity(G,+), *, y)) by Tautology.from(lastStep, step1)
            
            // 2. so (x + (-x))y = 0
            have(op(identity(G,+), *, y) === identity(G,+)) by Tautology.from(absorbingElementZero of (x -> y))
            val eq2 = have(op(op(x, +, minus(x)), *, y) === identity(G, +)) by Tautology.from(lastStep, eq1, equalityTransitivity of (x -> op(op(x, +, minus(x)), *, y), y -> op(identity(G,+), *, y), z -> identity(G, +)))

            // 3. ((x + (-x))y = xy + (-x)y) ==> ((-x)y + xy = 0)
            have(op(op(x, +, minus(x)), *, y) === op(op(x,*,y),+,op(minus(x),*,y))) by Tautology.from(invInG, distributivity of (y -> minus(x), z -> y))
            val step2 = have( (op(op(x,*,y),+,op(minus(x),*,y))) === identity(G, +)) by Tautology.from(lastStep, eq2, equalityTransitivity of (x -> (op(op(x,*,y),+,op(minus(x),*,y))), y -> op(op(x, +, minus(x)), *, y), z -> identity(G, +)))
            have((op(op(x,*,y),+,op(minus(x),*,y))) === op(op(minus(x),*,y),+, op(x,*,y))) by Tautology.from(abelianGroupG, prod1InG, prod2InG, commutativity  of (* -> +, x -> op(minus(x),*,y), y -> op(x,*,y)))
            val eq3 = have(op(op(minus(x),*,y),+, op(x,*,y)) === identity(G, +)) by Tautology.from(lastStep, step2, equalityTransitivity of (x -> op(op(minus(x),*,y),+, op(x,*,y)), y -> (op(op(x,*,y),+,op(minus(x),*,y))), z -> identity(G, +)))

            // 4. xy = -((-x)y)
            val eq4 = have(op(x,*,y) === minus(op(minus(x),*,y))) by Tautology.from(prod1InG, prod2InG, lastStep, groupG, inverseTest of (* -> +, x -> op(minus(x),*,y), y -> op(x,*,y)))
            
            // 5. -(xy) = -(-((-x)y)), so (-xy) = (-x)y by involution
            have((op(x,*,y) === minus(op(minus(x),*,y))) |- (minus(op(x,*,y)) === minus(minus(op(minus(x),*,y))))) by Congruence
            val eq5 = have(minus(op(x,*,y)) === minus(minus(op(minus(x),*,y)))) by Tautology.from(lastStep, eq4)
            have(minus(minus(op(minus(x),*,y))) === op(minus(x),*,y)) by Tautology.from(lastStep, additiveInverseIsInvolutive of (x -> op(minus(x),*,y)), prod2InG)
            have(thesis) by Tautology.from(lastStep, eq5, equalityTransitivity of (x -> minus(op(x,*,y)), y -> minus(minus(op(minus(x),*,y))), z -> op(minus(x),*,y)))
        }

        have(thesis) by Tautology.from(firstProof, secondProof)
    }

    /**
     * Theorem --- In a ring, we have '(-x)(-y) = xy. 
     * Where '-x' and '-y' denote the additive inverse of 'x' and 'y' respectively.
     */
    val negationCancellation = Theorem((ring(G, +, *), x ∈ G,y ∈ G) |- op(minus(x),*,minus(y)) === op(x,*,y)
    ){
        assume(ring(G, +, *))
        assume(x ∈ G)
        assume(y ∈ G)
        val invXinG = have(minus(x) ∈ G) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +), inverseInGroup of (* -> +))
        
        // 1. (-x)(-y) = -((-x)y)
        val eq1 = have(minus(op(minus(x),*,y)) === op(minus(x),*,minus(y))) by Tautology.from(lastStep, negationDistribution of (x -> minus(x)))
        
        // 2. -((-x)y) = (-(-x))y
        val eq2 = have(minus(op(minus(x),*,y)) === op(minus(minus(x)),*,y)) by Tautology.from(invXinG, negationDistribution of (x -> minus(x)))
        
        // 3. -(-x) = x so we can conclude (-(-x))y = xy
        val step1 = have(minus(minus(x)) === x) by Tautology.from(additiveInverseIsInvolutive)
        have(minus(minus(x)) === x |- op(minus(minus(x)),*,y) === op(x,*,y)) by Congruence
        val eq3 = have(op(minus(minus(x)),*,y) === op(x,*,y)) by Tautology.from(lastStep, step1)

        // 4. (-x)(-y) = xy by transitivity of the previous results
        have(minus(op(minus(x),*,y)) === op(x,*,y)) by Tautology.from(lastStep, eq2, equalityTransitivity of (x -> minus(op(minus(x),*,y)), y -> op(minus(minus(x)),*,y), z -> op(x,*,y)))
        have(thesis) by Tautology.from(lastStep, eq1, equalityTransitivity of (x -> op(minus(x),*,minus(y)), y -> minus(op(minus(x),*,y)), z -> op(x,*,y)))
    }

    /**
     * Theorem --- In a ring, we have 'x(y - z) = xy - xz' and '(x - y)z = xz - yz'.
     * Where the notation's meaning is that 'x - y' denotes the operation 'x + (-y)', and '-y' denotes the additive inverse of y.
     */
    val distributivityWithNegation = Theorem( (ring(G, +, *), x ∈ G, y ∈ G, z ∈ G) |- ((op(x,*,op(y,+, minus(z))) === op(op(x,*,y),+,minus(op(x,*,z)))) /\ (op(op(x,+, minus(y)),*,z) === op(op(x,*,z),+, minus(op(y,*,z)))))
    ){
        assume(ring(G, +, *))
        assume(x ∈ G)
        assume(y ∈ G)
        assume(z ∈ G)

        // first equality : x(y - z) = xy - xz
        val firstProof = have((ring(G, +, *), x ∈ G, y ∈ G, z ∈ G) |- op(x,*,op(y,+, minus(z))) === op(op(x,*,y),+,minus(op(x,*,z)))) subproof {
            val invZinG = have(minus(z) ∈ G) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +), additiveInverseInRing of (x -> z))
            
            // 1. x(y + (-z)) = xy + x(-z) by distributivity 
            val eq1 = have(op(x,*,op(y,+, minus(z))) === op(op(x,*,y), +, op(x,*, minus(z)))) by Tautology.from(invZinG, distributivity of (z -> minus(z)))
            
            // 2. x(-z) = -(xz), so xy + x(-z) = xy + -(xz) 
            val step1 = have(op(x,*, minus(z)) === minus(op(x,*,z))) by Tautology.from(negationDistribution of (y -> z))
            have((op(x,*, minus(z)) === minus(op(x,*,z))) |- op(op(x,*,y), +, op(x,*, minus(z))) === op(op(x,*,y), +, minus(op(x,*,z)))) by Congruence
            val eq2 = have(op(op(x,*,y), +, op(x,*, minus(z))) === op(op(x,*,y), +, minus(op(x,*,z)))) by Tautology.from(lastStep, step1)
            
            // 3. we conclude by transitivity
            have(thesis) by Tautology.from(lastStep, eq1, equalityTransitivity of (x -> op(x,*,op(y,+, minus(z))), y -> op(op(x,*,y), +, op(x,*, minus(z))), z -> op(op(x,*,y),+,minus(op(x,*,z)))))
        }
       
        // second equality: (x - y)z = xz - yz
        val secondProof = have((ring(G, +, *), x ∈ G, y ∈ G, z ∈ G) |- op(op(x,+, minus(y)),*,z) === op(op(x,*,z),+, minus(op(y,*,z)))) subproof {
            val invYinG = have(minus(y) ∈ G) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +), additiveInverseInRing of (x -> y))
            
            // 1. (x + (-y))z = xz + (-y)z by distributivity
            val eq1 = have(op(op(x,+, minus(y)),*,z) === op(op(x,*,z),+, op(minus(y),*,z))) by Tautology.from(invYinG, distributivity of (y -> minus(y)))

            // 2. (-y)z = -(yz)
            val step1 = have(op(minus(y),*,z) === minus(op(y,*,z))) by Tautology.from(negationDistribution of (x -> y, y -> z))
            have(op(minus(y),*,z) === minus(op(y,*,z)) |- op(op(x,*,z),+, op(minus(y),*,z)) === op(op(x,*,z),+, minus(op(y,*,z)))) by Congruence
            val eq2 = have(op(op(x,*,z),+, op(minus(y),*,z)) === op(op(x,*,z),+, minus(op(y,*,z)))) by Tautology.from(lastStep, step1)

            // 3. we conclude by transitivity
            have(thesis) by Tautology.from(lastStep, eq1, equalityTransitivity of (x -> op(op(x,+, minus(y)),*,z), y -> op(op(x,*,z),+, op(minus(y),*,z)), z -> op(op(x,*,z),+, minus(op(y,*,z)))))
        }

        have(thesis) by Tautology.from(firstProof, secondProof)
    }

    /**
     * Theorem --- In a ring, '-(x + y) = (-x) + (-y)', for all 'x,y' in 'G'.
     * Where '-x' denotes the additive inverse of 'x'.
     */
    val additiveNegationDistribution = Theorem((ring(G, +, *), x ∈ G, y ∈ G) |- minus(op(x,+,y)) === op(minus(x),+,minus(y))
    ){
        assume(ring(G, +, *))
        assume(x ∈ G)
        assume(y ∈ G)
         
        val groupG = have(group(G, +)) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +))
        val abelianGroupG = have(abelianGroup(G, +)) by Tautology.from(ring.definition)
        val invInG = have(minus(y) ∈ G) by Tautology.from(additiveInverseInRing of (x -> y))
        val XinvInG = have(minus(x) ∈ G) by Tautology.from(additiveInverseInRing)
        val invSumInG = have(op(minus(y), +, minus(x)) ∈ G) by Tautology.from(groupG, invInG, XinvInG, groupIsClosedByProduct of (* -> +, x -> minus(y), y -> minus(x)))
        val sumInG = have(op(x,+,y) ∈ G) by Tautology.from(groupG, groupIsClosedByProduct of (* -> +))

        // 1. (x + y) + (-y) = x + (y + (-y)) 
        val eq1 = have(op(op(x,+,y), +, minus(y)) === op(x, +, op(y,+,minus(y)))) by Tautology.from(groupG, invInG, associativity of (* -> +, z -> minus(y)))
        
        // 2. so we can state that (x + y) + (-y) = x + 0 = x
        val step1 = have(op(y,+,minus(y)) === identity(G, +)) by Tautology.from(groupG, inverseCancellation of (* -> +, x -> y))
        have((op(y,+,minus(y)) === identity(G, +)) |- op(x, +, op(y,+,minus(y))) === op(x, +, identity(G, +))) by Congruence
        have(op(x, +, op(y,+,minus(y))) === op(x, +, identity(G, +))) by Tautology.from(lastStep, step1)
        val step2 = have(op(op(x,+,y), +, minus(y)) === op(x, +, identity(G, +))) by Tautology.from(lastStep, eq1, equalityTransitivity of (x -> op(op(x,+,y), +, minus(y)), y -> op(x, +, op(y,+,minus(y))), z ->  op(x, +, identity(G, +))))
        have(op(x, +, identity(G, +)) === x) by Tautology.from(groupG, identityNeutrality of (* -> +))
        val eq2 = have(op(op(x,+,y), +, minus(y)) === x) by Tautology.from(lastStep, step2, equalityTransitivity of (x -> op(op(x,+,y), +, minus(y)), y -> op(x, +, identity(G, +)), z -> x))

        // 3. ((x + y) + (-y)) + (-x) = x + (-x) = 0
        have((op(op(x,+,y), +, minus(y)) === x) |- op(op(op(x,+,y), +, minus(y)),+, minus(x)) === op(x,+,minus(x))) by Congruence
        val step3 = have(op(op(op(x,+,y), +, minus(y)),+, minus(x)) === op(x,+,minus(x))) by Tautology.from(lastStep, eq2)
        have(op(x,+,minus(x)) === identity(G, +)) by Tautology.from(groupG, inverseCancellation of (* -> +))
        val eq3 = have(op(op(op(x,+,y), +, minus(y)),+, minus(x)) === identity(G, +)) by Tautology.from(lastStep, step3, equalityTransitivity of (x -> op(op(op(x,+,y), +, minus(y)),+, minus(x)), y -> op(x,+,minus(x)), z -> identity(G, +)))
    
        // 4. ((x + y) + (-y)) + (-x) = (x + y) + ((-y) + (-x)) by associativity
        have(op(op(op(x,+,y), +, minus(y)),+, minus(x)) === op(op(x,+,y), +, op(minus(y), +, minus(x)))) by Tautology.from(groupG, invInG, XinvInG, sumInG, associativity of (* -> +, x -> op(x,+,y), y -> minus(y), z -> minus(x)))
        // 5. so (x + y) + ((-y) + (-x)) = 0 (by 3.)
        have(op(op(x,+,y), +, op(minus(y), +, minus(x))) === identity(G, +)) by Tautology.from(lastStep, eq3, equalityTransitivity of (x -> op(op(x,+,y), +, op(minus(y), +, minus(x))), y -> op(op(op(x,+,y), +, minus(y)),+, minus(x)), z -> identity(G, +)))

        // 6. -(x + y) = (-y) + (-x) = (-x) + (-y) by commutativity
        val eq6 = have(op(minus(y), +, minus(x)) === minus(op(x,+,y))) by Tautology.from(groupG, lastStep, sumInG, invSumInG, inverseTest of (* -> +, x -> op(x,+,y), y -> op(minus(y), +, minus(x))))
        have(op(minus(y), +, minus(x)) === op(minus(x), +, minus(y))) by Tautology.from(abelianGroupG, invInG, XinvInG, commutativity of (* -> +, x -> minus(y), y -> minus(x)))
        have(thesis) by Tautology.from(lastStep, eq6, equalityTransitivity of (x -> minus(op(x,+,y)), y -> op(minus(y), +, minus(x)), z -> op(minus(x), +, minus(y))))
    }   

    /**
     * Theorem --- In a ring '(G, +, *)', we have 'y + x = z + x ==> y = z', and x + y = x + z ==> y = z.
     */
    val AdditiveCancellationLaw = Theorem((ring(G, +, *), x ∈ G, y ∈ G, z ∈ G) |- (((op(x, +, y) === op(x, +, z)) ==> (y === z)) /\ ((op(y, +, x) === op(z, +, x)) ==> (y === z)))
    ){
        have(thesis) by Tautology.from(ring.definition, abelianGroup.definition of (* -> +), rightCancellation of (* -> +), leftCancellation of (* -> +))
    }


    // Minus axioms
    val addingAdditiveInverse = Theorem((ring(G, +, *), x ∈ G, y ∈ G, (op(x, +, y) === identity(G, +)))|- y === minus(x)) {
        assume(ring(G, +, *), x ∈ G, y ∈ G)
        assume(op(x, +, y) === identity(G, +))
        val p = have(inverse(x, G, +) ∈ G) by Tautology.from(additiveInverseInRing)
        val ab = have(abelianGroup(G, +)) by Tautology.from(ring.definition)
        val b = have((abelianGroup(G, +), x ∈ G, y ∈ G) |- op(x, +, y) === op(y, +, x)) by Tautology.from(ab,commutativity of (* -> +))
        val c = have(identity(G, +) === op(x, +, y)) by Restate
        val d = have((identity(G, +) === op(x, +, y)) /\ (op(x, +, y) === op(y, +, x))) by Tautology.from(c, ab, b)
        have(identity(G, +) === op(y, +, x)) by Tautology.from(d, equalityTransitivity of (x -> identity(G, +), y -> op(x, +, y), z -> op(y, +, x)))
        thenHave((op(y, +, x) === identity(G, +))) by Restate
        val i = have((op(x, +, y) === identity(G, +)) /\ (op(y, +, x) === identity(G, +))) by Tautology.from(lastStep, c)
        val h = have((op(x, +, inverse(x, G, +)) === identity(G, +)) /\ (op(inverse(x, G, +), +, x) === identity(G, +))) by Tautology.from(ab, abelianGroup.definition of (G -> G, * -> +), inverseCancellation of (* -> +))
        thenHave((op(x, +, inverse(x, G, +)) === identity(G, +)) /\ (identity(G, +) === op(inverse(x, G, +), +, x))) by Restate
        val u = have((op(y, +, x) === identity(G, +)) /\ (identity(G, +) === op(inverse(x, G, +), +, x))) by Tautology.from(lastStep, i)
        val k = have((op(y, +, x)) === (op(inverse(x, G, +), +, x))) by Tautology.from(lastStep, equalityTransitivity of (x -> op(y, +, x), y -> identity(G, +), z -> op(inverse(x, G, +), +, x)))
        have(thesis) by Tautology.from(k, p, AdditiveCancellationLaw of (x -> x, y -> y, z -> inverse(x, G, +)))

    }

    /**
     * Lemma --- Transitivity of implication
     */
    val implicationTransitivity = Lemma((p1 ==> p2, p2 ==> p3) |- p1 ==> p3
    ){
        have(thesis) by Tautology
    }

    /**
     * Theorem --- In an integral domain '(G, +, *)', if 'x'  is in 'G' and 'x' is different from '0', then
     * 'xy = xz ==> y = z, and yx = zx ==> y = z' for all 'y,z' in 'G'.
     * '0' denotes the identity element under the '+' operation.
     */
    val multiplicativeCancellationLaw = Theorem((integralDomain(G,+,*), x ∈ G, y ∈ G, z ∈ G, x =/= identity(G, +)) |- (op(x,*,y) === op(x,*,z) ==> (y === z)) /\ (op(y,*,x) === op(z,*,x) ==> (y === z))
    ){
        assume(integralDomain(G, +, *))
        assume(x ∈ G)
        assume(y ∈ G)
        assume(z ∈ G)
        assume(x =/= identity(G, +))

        val inv = minus(op(x,*,z))
        val inRing = have(ring(G, +, *)) by Tautology.from(integralDomain.definition)
        val groupG = have(group(G, +)) by Tautology.from(lastStep, ring.definition, abelianGroup.definition of (* -> +))
        val abelianGroupG = have(abelianGroup(G, +)) by Tautology.from(inRing, ring.definition)
        val invZinG = have(minus(z)∈ G) by Tautology.from(inRing, additiveInverseInRing of (x -> z))
        val prodInG = have(op(x,*,z) ∈ G) by Tautology.from(inRing, ringIsClosedByProduct of (y -> z))
        val invInG = have(inv ∈ G) by Tautology.from(lastStep, inRing, additiveInverseInRing of (x -> op(x,*,z)))
        val yPlusMinusZinG = have(op(y,+,minus(z)) ∈ G) by Tautology.from(invZinG, groupG, groupIsClosedByProduct of (* -> +, x -> y, y -> minus(z)))
        
        // First equality : xy = xz ==> y = z
        val firstResult = have((integralDomain(G,+,*), x ∈ G, y ∈ G, z ∈ G, x =/= identity(G, +)) |- (op(x,*,y) === op(x,*,z) ==> (y === z))) subproof {
            // 1. xy = xz ==> xy + -(xz) = 0
            have((op(x,*,y) === op(x,*,z)) |- (op(op(x,*,y), +, inv) === op(op(x,*,z), +, inv))) by Congruence      
            val step1 = thenHave((op(x,*,y) === op(x,*,z)) ==> (op(op(x,*,y), +, inv) === op(op(x,*,z), +, inv))) by Restate                                  
            have(op(op(x,*,z), +, inv) === identity(G, +)) by Tautology.from(groupG, invInG, prodInG, inverseCancellation of (* -> +, x -> op(x,*,z)))
            val eq1 = have((op(x,*,y) === op(x,*,z)) ==> (op(op(x,*,y), +, inv) === identity(G, +))) by Tautology.from(lastStep, step1, equalityTransitivity of (x -> op(op(x,*,y), +, inv), y -> op(op(x,*,z), +, inv), z -> identity(G, +)))
            
            // 2. xy = xz ==> xy + x(-z) = 0 by negationDistribution
            val step2 = have(inv === op(x, *, minus(z))) by Tautology.from(inRing, negationDistribution of (y -> z))
            have( (inv === op(x, *, minus(z))) |- (op(op(x,*,y), +, inv) === op(op(x,*,y), +, op(x, *, minus(z))))) by Congruence
            have(op(op(x,*,y), +, inv) === op(op(x,*,y), +, op(x, *, minus(z)))) by Tautology.from(lastStep, step2)
            val eq2 = have((op(x,*,y) === op(x,*,z)) ==> (op(op(x,*,y), +, op(x, *, minus(z))) === identity(G, +))) by Tautology.from(lastStep, eq1, equalityTransitivity of (x -> op(op(x,*,y), +, op(x, *, minus(z))), y -> op(op(x,*,y), +, inv), z -> identity(G, +)))
            
            // 3. xy = xz ==> x(y + (-z)) = 0
            have(op(op(x,*,y), +, op(x, *, minus(z))) === op(x,*,op(y,+,minus(z)))) by Tautology.from(inRing, invZinG, distributivity of (z -> minus(z)))
            val eq3 = have((op(x,*,y) === op(x,*,z)) ==> (op(x,*,op(y,+,minus(z))) === identity(G, +))) by Tautology.from(lastStep, eq2, equalityTransitivity of (x -> op(x,*,op(y,+,minus(z))), y -> op(op(x,*,y), +, op(x, *, minus(z))), z -> identity(G, +)))
            
            // 4. xy = xz ==> y + (-z) = 0 as x =/= 0
            have((op(x,*,op(y,+,minus(z))) === identity(G, +)) ==> ((x === identity(G, +)) \/ (op(y,+,minus(z)) === identity(G, +)))) by Tautology.from(yPlusMinusZinG, noZeroDivisors of (y -> op(y,+,minus(z))))
            val step4 = have((op(x,*,y) === op(x,*,z)) ==> ((x === identity(G, +)) \/ (op(y,+,minus(z)) === identity(G, +)))) by Tautology.from(lastStep, eq3, implicationTransitivity of (p1 -> (op(x,*,y) === op(x,*,z)), p2 -> (op(x,*,op(y,+,minus(z))) === identity(G, +)), p3 -> ((x === identity(G, +)) \/ (op(y,+,minus(z)) === identity(G, +)))))
            have(((x === identity(G, +)) \/ (op(y,+,minus(z)) === identity(G, +))) ==> (op(y,+,minus(z)) === identity(G, +))) by Restate
            val eq4 = have((op(x,*,y) === op(x,*,z)) ==> (op(y,+,minus(z)) === identity(G, +))) by Tautology.from(lastStep, step4, implicationTransitivity of (p1 -> (op(x,*,y) === op(x,*,z)), p2 -> ((x === identity(G, +)) \/ (op(y,+,minus(z)) === identity(G, +))), p3 -> (op(y,+,minus(z)) === identity(G, +))))    

            // 5. xy = xz ==> -y = -z
            have((op(y,+,minus(z)) === identity(G, +)) |- (minus(y) === (minus(z)))) by Tautology.from(groupG, invZinG, inverseTest of (* -> +, x -> y, y -> minus(z)))
            thenHave((op(y,+,minus(z)) === identity(G, +)) ==> (minus(y) === minus(z))) by Restate
            val eq5 = have((op(x,*,y) === op(x,*,z)) ==> (minus(y) === minus(z))) by Tautology.from(lastStep, eq4, implicationTransitivity of (p1 -> (op(x,*,y) === op(x,*,z)), p2 -> (op(y,+,minus(z)) === identity(G, +)), p3 -> (minus(y) === minus(z))))
            
            // 6. -y = -z ==> y = z
            val step6 = have((minus(y) === minus(z)) |- minus(minus(y)) === minus(minus(z))) by Congruence
            have(minus(minus(y)) === y) by Tautology.from(inRing, additiveInverseIsInvolutive of (x -> y))
            val step7 = have((minus(y) === minus(z)) ==> (y === minus(minus(z)))) by Tautology.from(lastStep, step6, equalityTransitivity of (x -> y, y -> minus(minus(y)), z -> minus(minus(z))))
            have(minus(minus(z)) === z) by Tautology.from(inRing, additiveInverseIsInvolutive of (x -> z))
            val eq6 = have((minus(y) === minus(z)) ==> (y === z)) by Tautology.from(lastStep, step7, equalityTransitivity of (x -> y, y -> minus(minus(z)), z -> z))
            
            // 7. -y = -z ==> y = z, so xy = yz ==> y = z
            have(thesis) by Tautology.from(lastStep, eq5, implicationTransitivity of (p1 -> (op(x,*,y) === op(x,*,z)), p2 -> (minus(y) === minus(z)) , p3 -> (y === z)))
        }
        
        // Second equality : yx = zx ==> z = y
        // Proof by using the first equality and the commutativity property of an integral domain (yx = xy and zx = xz)
        val secondResult = have((integralDomain(G,+,*), x ∈ G, y ∈ G, z ∈ G, x =/= identity(G, +)) |- (op(y,*,x) === op(z,*,x) ==> (y === z))) subproof {
            // 1. yx = xz ==> xy = xz
            have(op(x,*,y) === op(y,*,x)) by Tautology.from(integralDomain.definition, ringCommutativity)
            val eq1 = have((op(y,*,x) === op(x,*,z)) ==> (op(x,*,y) === op(x,*,z))) by Tautology.from(lastStep, equalityTransitivity of (x -> op(x,*,y), y -> op(y,*,x), z -> op(x,*,z)))
            
            // 2. yx = zx ==> xy = xz 
            have(op(x,*,z) === op(z,*,x)) by Tautology.from(integralDomain.definition, ringCommutativity of (y -> z))
            have((op(y,*,x) === op(z,*,x)) ==> (op(y,*,x) === op(x,*,z))) by Tautology.from(lastStep, equalityTransitivity of (x -> op(y,*,x), y -> op(z,*,x), z -> op(x,*,z)))
            val eq2 = have((op(y,*,x) === op(z,*,x)) ==> (op(x,*,y) === op(x,*,z))) by Tautology.from(lastStep, eq1, implicationTransitivity of (p1 -> (op(y,*,x) === op(z,*,x)), p2 -> (op(y,*,x) === op(x,*,z)), p3 -> (op(x,*,y) === op(x,*,z))))
            
            // 3. yx = zx ==> y = z by first equality and transitivity of implication relation
            have(thesis) by Tautology.from(lastStep, firstResult, implicationTransitivity of (p1 -> (op(y,*,x) === op(z,*,x)), p2 -> (op(x,*,y) === op(x,*,z)), p3 -> (y === z)))
        }

        have(thesis) by Tautology.from(firstResult, secondResult)
    }

    /**
     * Theorem --- In a ring '(G, +, *)' with identity , a multiplicative identity element is unique, 
     * i.e. if both `e * x = x * e = x` and `f * x = x * f = x` for all `x`, then `e = f`.
     */
    val multiplicativeIdentityUniqueness = Theorem(identityRing(G, +, *) |- ∃!(e, isNeutral(e, G, *))
    ) {
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

            // 3. f = e by transitivity
            have(thesis) by Tautology.from(firstEq, lastStep, equalityTransitivity of (x -> e, y -> op(e, *, f), z -> f))
        }
        have(thesis) by ExistenceAndUniqueness(isNeutral(e, G, *))(existence, uniqueness)    
    }

    /**
     * Defines the multiplicative identity element of `(G, +, *)`.
     */
    val multiplicativeIdentity = DEF(G, +, *) --> TheConditional(e, isNeutral(e, G, *))(multiplicativeIdentityUniqueness)

    //
    // 2. Subrings
    //

    // By convention, this will always refer to the restricted operations.
    private val ★ = restrictedFunction(+, cartesianProduct(H, H))
    private val ♦ = restrictedFunction(*, cartesianProduct(H, H))

    /**
     * Subring --- `H` is a subring of `(G, +, *)` if `H` is a subset of `G`, such that `(H, ★, ♦)` is a ring.
     *
     * We will denote `H <= G` for `H` a subring of `G`.
     */
    val subring = DEF(H, G, +, *) --> ring(G, +, *) /\ subset(H, G) /\ ring(H, restrictedFunction(+, cartesianProduct(H, H)), restrictedFunction(*, cartesianProduct(H, H)))

    
    //
    // 3. Group of units
    //

    // By convention, this will always refer to the restricted operations on the group of units 'U'.
    private val opU = restrictedFunction(*, cartesianProduct(U, U))
    
    // if an element has an inverse under '*' in 'G', then it is in the group of units 'U'.
    private val allUnitsIncluded = DEF(U, G, *) --> ∀(x, (x ∈ G) /\ ∃(y, isInverse(y, x, G, *)) ==> (x ∈ U))

    /**
     * Group of units --- 'U' is the group of units of '(G, +, *)' if all the invertible elements under '*' of 'G' are in 'U',
     * and 'U' is a group under the operator '*'.
     */
    val unitGroup = DEF(U, G, +, *) --> ring(G, +, *) /\ group(U, opU) /\ allUnitsIncluded(U, G, *) /\ subset(U, G)

    /**
     * Definition of the x^(-1) in a ring.
     * 'x^(-1)' is the multiplicative inverse of 'x' in 'G'.
     */
    inline def multiplicativeInverse(x: Term) = inverse(x, U, opU)

    /**
     * Lemma --- If an element is in the group of units, then it has an inverse under the binary operation '*', restricted to 'U'.
     * 
     * Practical reformulation of [[allUnitsIncluded]]
     */
    val hasInverse = Lemma( (unitGroup(U, G, +, *), x ∈ U) |- ∃(y, isInverse(y, x, U, opU))
    ){
        have(group(U, opU) |- ∀(x, x ∈ U ==> ∃(y, isInverse(y, x, U, opU)))) by Tautology.from(unitGroup.definition, group.definition of(G -> U, * -> opU), inverseExistence.definition of(G -> U, * -> opU))
        have(unitGroup(U, G, +, *) |- ∀(x, x ∈ U ==> ∃(y, isInverse(y, x, U, opU)))) by Tautology.from(lastStep, unitGroup.definition)
        thenHave(unitGroup(U, G, +, *) |- (x ∈ U ==> ∃(y, isInverse(y, x, U, opU)))) by InstantiateForall(x)
        thenHave(thesis) by Restate
    }

    /**
     * Lemma --- If an element in the structure '(G, +, *)' has an inverse, then it is in the group of units 'U'.
     */
    val inverseInUnitGroup = Lemma((unitGroup(U, G, +, *), x ∈ G) |- ((∃(y, isInverse(y, x, G, *))) ==> x ∈ U)
    ){
        have(unitGroup(U, G, +, *) |- ∀(x, (x ∈ G) /\ ∃(y, isInverse(y, x, G, *)) ==> (x ∈ U))) by Tautology.from(unitGroup.definition, allUnitsIncluded.definition)
        thenHave(thesis) by InstantiateForall(x)
    }

    /**
     * Theorem --- When it exists, the multiplicative inverse of `x` (i.e. `y` such that `x * y = y * x = e`) in a ring is unique.
     */
    val multiplicativeInverseUniqueness = Theorem((unitGroup(U, G, +, *), x ∈ U) |- ∃!(y, isInverse(y, x, U, opU))
    ){
        have(thesis) by Tautology.from(unitGroup.definition, inverseUniqueness of (G -> U, * -> opU))
    }

    /**
     * Lemma --- When it exists, the multiplicative inverse of 'x' is the multiplicative inverse of 'x'. 
     * (by definition of the group of units)
     */
    val multiplicativeInverseIsInverse = Lemma( (unitGroup(U, G, +, *), x ∈ U) |- isInverse(multiplicativeInverse(x), x, U, opU)
    ){
        have(thesis) by Tautology.from(unitGroup.definition, inverseIsInverse of (G -> U, * -> opU))
    }

    /**
     * Lemma --- When it exists, the multiplicative inverse of 'x' in the ring '(G, +, *)', is in the group of units 'U'.
     */
    val multiplicativeInverseInU = Lemma((unitGroup(U, G, +, *), x ∈ U) |- multiplicativeInverse(x) ∈ U
    ){
        assume(unitGroup(U, G, +, *))
        assume(x ∈ U)
        have(isInverse(multiplicativeInverse(x), x, U, opU)) by Tautology.from(multiplicativeInverseIsInverse)
        have(thesis) by Tautology.from(lastStep, isInverse.definition of (y -> multiplicativeInverse(x), G -> U, * -> opU))
    }

    /**
     * Lemma --- When it exists, the multiplicative inverse of 'x' is in the ring '(G, +, *)'.
     */
    val multiplicativeInverseInRing = Lemma((unitGroup(U, G, +, *), x ∈ U) |- multiplicativeInverse(x) ∈ G
    ){
        assume(unitGroup(U, G, +, *))
        assume(x ∈ U)
        val z = multiplicativeInverse(x)
        val inverseInU = have(z ∈ U) by Tautology.from(multiplicativeInverseInU)
        // U is a subset of G, and x^(-1) is in U, so it's in G.
        have(∀(x, x ∈ U ==> x ∈ G)) by Tautology.from(unitGroup.definition, subset.definition of (x -> U, y -> G))
        thenHave(x ∈ U ==> x ∈ G) by InstantiateForall(x)
        have(thesis) by Tautology.from(lastStep of (x -> z), inverseInU)
    }
    
    /**
     * Theorem --- When it exists, `y` is the inverse of `x` iff `x` is the inverse of `y`.
     */
    val multiplicativeInverseSymmetry = Theorem((unitGroup(U, G, +, *), x ∈ U, y ∈ U) |- (y === multiplicativeInverse(x)) <=> (x === multiplicativeInverse(y))
    ){
        have(thesis) by Tautology.from(unitGroup.definition, inverseSymmetry of (G -> U, * -> opU))
    }
    
    /**
     * Theorem --- For all 'x', multiplicativeInverse(multiplicativeInverse(x)) = x
     * 
     * Direct corollary of [[multiplicativeInverseSymmetry]].
     */
    val multiplicativeInverseIsInvolutive = Theorem((unitGroup(U, G, +, *), x ∈ U) 
    |- multiplicativeInverse((multiplicativeInverse(x))) === x
    ){
        assume(unitGroup(U, G, +, *))
        assume(x ∈ U)
        have(thesis) by Tautology.from(multiplicativeInverseSymmetry of (y -> multiplicativeInverse(x)), multiplicativeInverseInU)
    }
    
    //
    // 4. Ring Homomorphism
    //

    // Extra group composition law
    private val -+ = variable
    private val -* = variable

    /**
     * Definition --- A ring homomorphism is a mapping `f: G -> H` from ring structures '(G, +, *)' and '(H, -+, -*)' equipped with binary operations `+`, '*', '-+' and `-*` respectively,
     * such that for all `x, y ∈ G`, we have `f(x * y) = f(x) -* f(y)` and 'f(x + y) = f(x) -+ f(y)'.
     *
     */
    val ringHomomorphism = DEF(f, G, +, *, H, -+, -*) --> ring(G, +, *) /\ ring(H, -+, -*) /\ functionFrom(f, G, H) /\ ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y))))) /\ ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y)))))
    
    /**
     * Lemma --- Practical reformulation of the homomorphism definition.
     */
    val ringHomomorphismApplication = Lemma((ringHomomorphism(f, G, +, *, H, -+, -*), x ∈ G, y ∈ G) |- ((app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y))) /\ (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y))))
    ){
        assume(ringHomomorphism(f, G, +, *, H, -+, -*))
        val init = have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y))))) /\ ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y)))))) by Tautology.from(ringHomomorphism.definition)
        
        thenHave(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y)))))) by Weakening
        thenHave((x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y)))))) by InstantiateForall(x)
        thenHave((x ∈ G) |- ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y))))) by Restate
        val multiplication = thenHave((x ∈ G) |- y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), -*, app(f, y)))) by InstantiateForall(y)
        
        have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y)))))) by Weakening(init)
        thenHave((x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y)))))) by InstantiateForall(x)
        thenHave((x ∈ G) |- ∀(y, y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y))))) by Restate
        thenHave((x ∈ G) |- y ∈ G ==> (app(f, op(x, +, y)) === op(app(f, x), -+, app(f, y)))) by InstantiateForall(y)

        have(thesis) by Tautology.from(multiplication, lastStep)
    }


    /**
     * Lemma --- If `f` is a ring homomorphism, then `f(x) ∈ H` for all `x ∈ G`.
     */
    val imageInCodomain = Lemma((ringHomomorphism(f, G, +, *, H, -+, -*), z ∈ G) |- app(f, z) ∈ H 
    ){ 
        have(ringHomomorphism(f, G, +, *, H, -+, -*) |- functionFrom(f,G,H)) by Tautology.from(ringHomomorphism.definition)
        have(thesis) by Tautology.from(lastStep, functionAppInCodomain of (x -> G, y -> H, t -> z)) 
    }
        
    
    /**
     * Theorem --- If `f` is a ring homomorphism between `G` and `H`, then `f(0_G) = 0_H`.
     * Where 0_G and 0_H are the additive identity elements in' G' and 'H' respectively
     */
    val ringHomomorphismMapsZeroToZero = Theorem((ringHomomorphism(f, G, +, *, H, -+, -*)) |- (app(f, identity(G,+)) === identity(H, -+))
    ){
        assume(ringHomomorphism(f, G, +, *, H, -+, -*))
        val e = identity(G, +)
        val groupG = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- group(G, +)) by Tautology.from(ringHomomorphism.definition, ring.definition, abelianGroup.definition of (* -> +))
        val groupH = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- group(H, -+)) by Tautology.from(ringHomomorphism.definition, ring.definition of (G -> H, this.+ -> -+, * -> -*), abelianGroup.definition of (G -> H, * -> -+))
        val identityInG = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- e ∈ G) by Tautology.from(groupG, identityInGroup of (* -> +))
        val appInH = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- app(f, e) ∈ H) by Tautology.from(identityInG, imageInCodomain of (z -> e))

        // 1. e + e = e 
        have(group(G, +) |- op(e, +, e) === e) by Tautology.from(identityInGroup of (* -> +), identityIdempotence of (* -> +, x -> e))
        val eq1 = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- op(e, +, e) === e) by Tautology.from(groupG, lastStep)

        // 2. f(e + e) = f(e)
        have(op(e, +, e) === e |- app(f, op(e, +, e)) === app(f, e)) by Congruence 
        have(ringHomomorphism(f, G, +, *, H, -+, -*) |- app(f, op(e, +, e)) === app(f, e)) by Tautology.from(eq1, lastStep)
        val eq2 = thenHave(ringHomomorphism(f, G, +, *, H, -+, -*) |- app(f, e) === app(f, op(e, +, e))) by Restate
        
        // 3. f(e + e) = f(e) -+ f(e)
        val eq3 = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- app(f, op(e, +, e)) === op(app(f, e), -+, app(f, e))) by Tautology.from(identityInG, ringHomomorphismApplication of (x -> e, y -> e))

        // 4. f(e) -+ f(e) = f(e)
        val eq4 = have(ringHomomorphism(f, G, +, *, H, -+, -*) |- op(app(f, e), -+, app(f, e)) === app(f, e)) by Tautology.from(eq2, eq3, equalityTransitivity of (x -> app(f, e), y -> app(f, op(e, +, e)), z -> op(app(f, e), -+, app(f, e))))

        // Conclude by idempotence
        have((ringHomomorphism(f, G, +, *, H, -+, -*), app(f, e) ∈ H) |- (op(app(f, e), -+, app(f, e)) === app(f, e)) <=> (app(f, e) === identity(H, -+))) by Tautology.from(groupH, identityIdempotence of (x -> app(f, e), G -> H, * -> -+))
        have(ringHomomorphism(f, G, +, *, H, -+, -*) |- (op(app(f, e), -+, app(f, e)) === app(f, e)) <=> (app(f, e) === identity(H, -+))) by Tautology.from(appInH,lastStep)
        have(thesis) by Tautology.from(lastStep, eq4)
    }
       
}
