
module DeepInductionGADTs-Seq-G-Fin-Vec where 


open import Level using (Lift ; lift)
open import Data.Product 
open import Data.Unit
open import Data.Empty
open import Agda.Builtin.Nat

data Eq : Set → Set → Set where 
  rfl : ∀ {A} → Eq A A 

data Seq  : Set → Set₁ where 
  const : ∀ {A : Set} → A → Seq A
  spair : ∀ {A} B C → Eq A (B × C) → Seq B → Seq C → Seq A

Pair^ : ∀ {A B : Set} → (A → Set) → (B → Set) → (A × B → Set)
Pair^ Pa Pb (x , y) = Pa x × Pb y

Eq^ : ∀ (A B : Set) → (A → Set) → (B → Set) → (Eq A B → Set)
Eq^ A .A Pa Pb rfl = ∀ x → Eq (Pa x) (Pb x)

-- exists (x : A). P x 
-- Σ A (λ x → P x)
-- (x , Px )

-- spair clause of Seq^ has type Set₁ because it quantifies over (B → Set) of type Set₁ 
-- so Seq^ must return an element of Set₁ in both cases 
Seq^ : ∀ (A : Set) → (A → Set) → Seq A → Set₁
Seq^ A P (const x) = Lift _ (P x) -- need to use Lift to get into Set₁
Seq^ A P (spair B C e sb sc) = Σ ((B → Set) × (C → Set)) (λ { (Pb , Pc) → Eq^ A (B × C) P (Pair^ Pb Pc) e × Seq^ B Pb sb × Seq^ C Pc sc })
  -- this expression represents:
  --  exists (Pb : B → Set) (Pc : C → Set). 
  --     (Eq^  A (B × C) P (Pair^ Pb Pc) e) × (Seq^ B Pb sb) × (Seq^ C Pc sc)
  -- 
  -- an element of this type has the form: 
  -- ((Pb , Pc) , eq , S^B , S^C)
  -- where Pb  : B → Set
  --       Pc  : C → Set
  --       eq  : Eq^ (B × C) (B × C) P (Pair^ Pb Pc) rfl
  --       S^B : Seq^ B Pb sb 
  --       S^C : Seq^ C Pc sc
  -- 

EqDindSeq : ∀ (P : ∀ (A : Set) → (A → Set) → Seq A → Set) 
            → (∀ (A : Set) (Pa : A → Set) (x : A) → Pa x → P A Pa (const x))
            → (∀ (A B C : Set) (Pa : A → Set) (Pb : B → Set) (Pc : C → Set) 
                 (e : Eq A (B × C)) (x : Seq B) (y : Seq C) 
               → Eq^ A (B × C) Pa (Pair^ Pb Pc) e → P B Pb x → P C Pc y 
               → P A Pa (spair B C e x y))
            → ∀ (A : Set) (Pa : A → Set) (x : Seq A) → Seq^ A Pa x → P A Pa x
EqDindSeq P PConst PPair A        Pa  (const x)             (lift Px) = PConst A Pa x Px
EqDindSeq P PConst PPair A Pbc (spair B C e sb sc) ((Pb , Pc) , eq-Pbc-Pb×Pc , S^B , S^C ) = 
  let PBsb : P B Pb sb
      PBsb = EqDindSeq P PConst PPair B Pb sb S^B
      PCsc : P C Pc sc
      PCsc = EqDindSeq P PConst PPair C Pc sc S^C
    in PPair A B C Pbc Pb Pc e sb sc eq-Pbc-Pb×Pc PBsb PCsc 

-------------------------------------------------
-------------- Deep induction for G ------------- 
-------------------------------------------------

K1 : (A : Set) → Set
K1 _ = ⊤

-- 'lift' Pa to constantly true predicate 
K1^ : ∀ {A : Set} → (A → Set) → K1 A → Set
K1^ Pa tt = ⊤

data G : Set → Set₁ where 
  -- c : ∀ {A} → Eq A ⊤ → G A 
  c : ∀ {A} B → Eq A (K1 B) → G A

G^ : ∀ (A : Set) → (A → Set) → G A → Set₁
G^ A P (c B e) = Σ (B → Set) (λ Pb → Eq^ A (K1 B) P (K1^ Pb) e)


EqDindG : ∀ (P : ∀ (A : Set) → (A → Set) → G A → Set)
          → (∀ (A : Set) (B : Set) (Pa : A → Set) (Pb : B → Set) (e : Eq A (K1 B)) 
             → Eq^ A (K1 B) Pa (K1^ Pb) e → P A Pa (c B e))
          → ∀ (A : Set) (Pa : A → Set) (x : G A) → G^ A Pa x → P A Pa x
EqDindG P Pc A Pa (c B e) (Pb , eq-P-K1^Pb) = Pc A B Pa Pb e eq-P-K1^Pb 


--------------------------------------------------
------------- Deep induction for Fin -------------
--------------------------------------------------


data Z : Set where 
data S : Set → Set where 

data Fin : Set → Set₁ where 
  FinZ : ∀ {A} B → Eq A (S B) → Fin A
  FinS : ∀ {A} B → Eq A (S B) → Fin B → Fin A

-- S A is uninhabited, so we can match it with 'absurd pattern' (). 
-- Intuitively, S^ P gives the predicate on the empty set. 
S^ : ∀ {A : Set} → (A → Set) → S A → Set
S^ P () 

Fin^ : ∀ (A : Set) → (A → Set) → Fin A → Set₁
Fin^ A _P (FinZ B e)    = Σ (B → Set) (λ Pb → Eq^ A (S B) _P (S^ Pb) e)
Fin^ A _P (FinS B e fb) = Σ (B → Set) (λ Pb → Eq^ A (S B) _P (S^ Pb) e × Fin^ B Pb fb) 

EqDindFin : ∀ (P : ∀ (A : Set) → (A → Set) → Fin A → Set)
          → (∀ (A : Set) (B : Set) (Pa : A → Set) (Pb : B → Set) (e : Eq A (S B))
             → Eq^ A (S B) Pa (S^ Pb) e → P A Pa (FinZ B e))
          → (∀ (A : Set) (B : Set) (Pa : A → Set) (Pb : B → Set) (e : Eq A (S B)) (fb : Fin B)
             → Eq^ A (S B) Pa (S^ Pb) e → P B Pb fb → P A Pa (FinS B e fb))
          → ∀ (A : Set) (Pa : A → Set) (x : Fin A) → Fin^ A Pa x → P A Pa x
EqDindFin P PFinZ PFinS A Pa (FinZ B e) (Pb , eq-P-S^Pb) = 
    PFinZ A B Pa Pb e eq-P-S^Pb

EqDindFin P PFinZ PFinS A Pa (FinS B e fb) (Pb , eq-P-S^Pb , F^B ) = 
    PFinS A B Pa Pb e fb eq-P-S^Pb (EqDindFin P PFinZ PFinS B Pb fb F^B) 

-- what kind of predicates can we have on Fin?
-- 
-- we can encode 'even' as follows
-- 
-- note the predicate _Pa is not used because Fin does not contain any elements of its type parameter A. 
FinPred : ∀ (A : Set) → (A → Set) → Fin A → Set
FinPred A _Pa (FinZ B e) = ⊤ -- true for 0
FinPred A _Pa (FinS B e (FinZ B₁ e₁)) = ⊥ -- false for 1
FinPred .(S (S B)) _Pa (FinS .(S B) rfl (FinS B rfl fb)) = FinPred B (λ _ → ⊤) fb 

--------------------------------------------------
------------- Deep induction for Vec -------------
--------------------------------------------------

{-
This version of Vec doesn't precisely follow the form we have been using. 
Instead of Eq N Z, we should have Eq N (KZ M) for some existentially quantified M.
The version with (KZ M) is shown below this commented block.

data Vec : Set → Set → Set₁ where 
  VNil  : ∀ {A N} → Eq N Z → Vec A N
  VCons : ∀ {A N} M → Eq N (S M) → A → Vec A M → Vec A N

-- trivial lifting for Z 
Z^ : ∀ {A : Set} → (A → Set) → Z → Set 
Z^ P ()

Vec^ : ∀ (A N : Set) → (A → Set) → (N → Set) → Vec A N → Set₁
Vec^ A N Pa Pn (VNil e) = Lift _ (Eq^ N Z Pn (Z^ Pn) e)
Vec^ A N Pa Pn (VCons M e x xs) = Σ (M → Set) 
                                   (λ Pm → Eq^ N (S M) Pn (S^ Pm) e × Pa x × Vec^ A M Pa Pm xs ) 

-- I think predicates on length parameter will all be trivial, so this should effectively 
-- be deep induction for lists... 
EqDindVec : ∀ (P : ∀ (A : Set) (N : Set) → (A → Set) → (N → Set) → Vec A N → Set)
            → (∀ (A : Set) (N : Set) (Pa : A → Set) (Pn : N → Set) (e : Eq N Z) 
               → Eq^ N Z Pn (Z^ Pn) e → P A N Pa Pn (VNil e))
            → (∀ (A : Set) (N : Set) (M : Set) (Pa : A → Set) (Pn : N → Set) (Pm : M → Set)
                 (e : Eq N (S M)) (x : A) (xs : Vec A M) 
                 → Eq^ N (S M) Pn (S^ Pm) e 
                 → Pa x → P A M Pa Pm xs → P A N Pa Pn (VCons M e x xs))
            → ∀ (A N : Set) (Pa : A → Set) (Pn : N → Set) (xs : Vec A N) → Vec^ A N Pa Pn xs → P A N Pa Pn xs
EqDindVec P PNil PCons A N Pa Pn (VNil e) (lift eq-Pn-Z^Pn) = PNil A N Pa Pn e eq-Pn-Z^Pn
EqDindVec P PNil PCons A N Pa Pn (VCons M e x xs) (Pm , eq-Pn-S^Pm , Pax , V^xs) = 
  PCons A N M Pa Pn Pm e x xs eq-Pn-S^Pm Pax (EqDindVec P PNil PCons A M Pa Pm xs V^xs) 
-}

KZ : Set → Set
KZ _ = Z

data Vec : Set → Set → Set₁ where 
  VNil  : ∀ {A N} M → Eq N (KZ M) → Vec A N
  VCons : ∀ {A N} M → Eq N  (S M) → A → Vec A M → Vec A N

KZ^ : ∀ {A : Set} → (A → Set) → KZ A → Set 
KZ^ P ()

Vec^ : ∀ (A N : Set) → (A → Set) → (N → Set) → Vec A N → Set₁
Vec^ A N Pa Pn (VNil M e) = Σ (M → Set) (λ Pm → Eq^ N Z Pn (KZ^ Pm) e)
Vec^ A N Pa Pn (VCons M e x xs) = Σ (M → Set) 
                                   (λ Pm → Eq^ N (S M) Pn (S^ Pm) e × Pa x × Vec^ A M Pa Pm xs ) 

-- I think predicates on length parameter will all be trivial, so this should effectively 
-- be deep induction for lists... 
EqDindVec : ∀ (P : ∀ (A : Set) (N : Set) → (A → Set) → (N → Set) → Vec A N → Set)
            → (∀ (A : Set) (N : Set) (M : Set) (Pa : A → Set) (Pn : N → Set) (Pm : M → Set) (e : Eq N Z) 
               → Eq^ N Z Pn (KZ^ Pm) e → P A N Pa Pn (VNil M e))
            → (∀ (A : Set) (N : Set) (M : Set) (Pa : A → Set) (Pn : N → Set) (Pm : M → Set)
                 (e : Eq N (S M)) (x : A) (xs : Vec A M) 
                 → Eq^ N (S M) Pn (S^ Pm) e 
                 → Pa x → P A M Pa Pm xs → P A N Pa Pn (VCons M e x xs))
            → ∀ (A N : Set) (Pa : A → Set) (Pn : N → Set) (xs : Vec A N) → Vec^ A N Pa Pn xs → P A N Pa Pn xs
EqDindVec P PNil PCons A N Pa Pn (VNil M e) (Pm , eq-Pn-KZ^Pm) = PNil A N M Pa Pn Pm e eq-Pn-KZ^Pm
EqDindVec P PNil PCons A N Pa Pn (VCons M e x xs) (Pm , eq-Pn-S^Pm , Pax , V^xs) = 
  PCons A N M Pa Pn Pm e x xs eq-Pn-S^Pm Pax (EqDindVec P PNil PCons A M Pa Pm xs V^xs) 
