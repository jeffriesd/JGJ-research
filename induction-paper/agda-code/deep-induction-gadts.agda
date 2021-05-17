{-# OPTIONS --injective-type-constructors #-}

module deep-induction-gadts where

open import Data.Product using (_×_ ; _,_ ; Σ-syntax ; ∃-syntax)
open import Data.List renaming ([] to nil ; _∷_ to cons)
open import Data.Unit using (⊤ ; tt) 
open import Data.Bool using (Bool ; true ; false) 
open import Data.String using (String)
open import Data.Maybe using (Maybe ; just ; nothing) 

open import Level renaming (suc to lsuc ; zero to lzero)

-- Introduction

data Rose : Set → Set where
  empty : ∀ {A : Set} → Rose A
  node  : ∀ {A : Set} → A → List (Rose A) → Rose A

-- lifting of predicates for List 
List^ : ∀ {a} {l} (A : Set a) → (A → Set l) → List A → Set l
List^ A Qa nil = Lift _ ⊤
List^ A Qa (cons x xs) = Qa x × (List^ A Qa xs)

-- Pred A is the type of predicates on A valued in the l'th universe.
Pred : ∀ {l} {a} → (A : Set a) → Set _
Pred {l} A = A → Set l

-- PredMap A Q Q' is the type of morphisms from Q to Q' 
PredMap : ∀ {l1 l2} {a} (A : Set a) → Pred {l1} A → Pred {l2} A → Set _
PredMap A Q Q' = ∀ (x : A) → Q x → Q' x

-- take a morphism of predicates from Q to Q' and return a morphism of predicates from (List^ A Q) to (List^ A Q') 
liftListMap : ∀ {a} {l1 l2} (A : Set a) → (Q : A → Set l1) → (Q' : A → Set l2) → PredMap A Q Q' → PredMap (List A) (List^ A Q) (List^ A Q')
liftListMap A Q Q' m nil _ = lift tt
liftListMap A Q Q' m (cons a l') (y , x') = (m a y , liftListMap A Q Q' m l' x')

-- equation 1
--
-- structural induction rule for Rose 
{-# TERMINATING #-}
Rose^ : ∀ (A : Set) → (A → Set) → Rose A → Set
Rose^ A P empty = ⊤
Rose^ A P (node a ts) = P a × List^ (Rose A) (Rose^ A P) ts 

{-# TERMINATING #-}
indRose : ∀ (A : Set) (P : Rose A → Set) (Q : A → Set)
          → P empty
          → (∀ (a : A) (ts : List (Rose A)) → Q a → List^ (Rose A) P ts → P (node a ts))
          → ∀ (x : Rose A) → Rose^ A Q x → P x 
indRose A P Q cempty cnode empty liftR = cempty
indRose A P Q cempty cnode (node a ts) (Pa , liftts) = cnode a ts Pa prose 
  where prose : List^ (Rose A) P ts
        prose = liftListMap (Rose A) (Rose^ A Q) P (indRose A P Q cempty cnode) ts liftts 

-- equation 2
data Seq' : Set → Set₁ where
  const : ∀ {A : Set} → A → Seq' A
  pair  : ∀ {A B : Set} → Seq' A → Seq' B → Seq' (A × B)


-- 2 . Deep induction for ADTs and nested types


-- structural induction for lists
indList : ∀ (A : Set) (P : List A → Set) → P nil
           → (∀ (a : A) (as : List A) → P as → P (cons a as))
           → ∀ (as : List A) → P as
indList A P cnil ccons nil = cnil
indList A P cnil ccons (cons a as) = ccons a as (indList A P cnil ccons as)

-- deep induction for lists 
dIndList : ∀ (A : Set) (P : List A → Set) (Q : A → Set)
           → P nil
           → (∀ (a : A) (as : List A) → Q a → P as → P (cons a as))
           → ∀ (as : List A) → List^ A Q as → P as
dIndList A P Q cnil ccons nil _ = cnil 
dIndList A P Q cnil ccons (cons a as) (Qa , liftas) = ccons a as Qa (dIndList A P Q cnil ccons as liftas)



data PTree : Set → Set where
  pleaf : ∀ {A : Set} → A → PTree A
  pnode : ∀ {A : Set} → PTree (A × A) → PTree A


-- lifting of predicates to pairs
Pair^ : ∀ {l} {a} {b} → (A : Set a) → (B : Set b) → (A → Set l) → (B → Set l) → (A × B → Set l)
Pair^ A B Qa Qb (x , y) = Qa x × Qb y

indPTree : ∀ (P : ∀ (A : Set) → PTree A → Set)
           → (∀ (A : Set) (a : A) → P A (pleaf a))
           → (∀ (A : Set) (pp : PTree (A × A)) → P (A × A) pp → P A (pnode pp))
           → ∀ (A : Set) (p : PTree A) → P A p
indPTree P spleaf spnode A (pleaf a) = spleaf A a
indPTree P spleaf spnode A (pnode pp) = spnode A pp (indPTree P spleaf spnode (A × A) pp)


PTree^ : ∀ (A : Set) → (A → Set) → PTree A → Set
PTree^ A Qa (pleaf x) = Qa x
PTree^ A Qa (pnode pt) = PTree^ (A × A) (Pair^ A A Qa Qa) pt

dIndPTree : ∀ (P : ∀ (A : Set) → (A → Set) → PTree A → Set)
            → (∀ (A : Set) (Q : A → Set) (a : A) → Q a → P A Q (pleaf a))
            → (∀ (A : Set) (Q : A → Set) (pp : PTree (A × A)) → P (A × A) (Pair^ A A Q Q) pp → P A Q (pnode pp))
            → ∀ (A : Set) (Q : A → Set) (p : PTree A) → PTree^ A Q p → P A Q p
dIndPTree P cpleaf cpnode A Q (pleaf a) Qa = cpleaf A Q a Qa
dIndPTree P cpleaf cpnode A Q (pnode pp) liftpp = cpnode A Q pp (dIndPTree P cpleaf cpnode (A × A) (Pair^ A A Q Q) pp liftpp)


{-# NO_POSITIVITY_CHECK #-}
data Bush : Set → Set where
  bnil  : ∀ {A : Set} → Bush A
  bcons : ∀ {A : Set} → A → Bush (Bush A) → Bush A


{-# TERMINATING #-}
Bush^ : ∀ (A : Set) → (A → Set) → Bush A → Set
Bush^ A Q bnil = ⊤
Bush^ A Q (bcons a bb) = Q a × Bush^ (Bush A) (Bush^ A Q) bb

{-# TERMINATING #-}
liftBushMap : ∀ (A : Set) (Q Q' : A → Set) → PredMap A Q Q' → PredMap (Bush A) (Bush^ A Q) (Bush^ A Q')
liftBushMap A Q Q' m bnil _ = tt
liftBushMap A Q Q' m (bcons a bb) (Qa , liftbb) =
  (m a Qa) , (liftBushMap (Bush A) (Bush^ A Q) (Bush^ A Q') (liftBushMap A Q Q' m) bb liftbb)


{-# TERMINATING #-}
dIndBush : ∀ (P : ∀ (A : Set) → (A → Set) → Bush A → Set)
           → (∀ (A : Set) (Q : A → Set) → P A Q bnil)
           → (∀ (A : Set) (Q : A → Set) (a : A) (bb : Bush (Bush A)) → Q a → P (Bush A) (P A Q) bb
                → P A Q (bcons a bb))
           → ∀ (A : Set) (Q : A → Set) (b : Bush A) → Bush^ A Q b → P A Q b
dIndBush P cbnil cbcons A Q bnil tt = cbnil A Q
dIndBush P cbnil cbcons A Q (bcons a bb) (Qa , liftbb) = cbcons A Q a bb Qa (dIndBush P cbnil cbcons (Bush A) (P A Q) bb liftPbb)
  where liftPbb : Bush^ (Bush A) (P A Q) bb
        liftPbb = liftBushMap (Bush A) (Bush^ A Q) (P A Q) (dIndBush P cbnil cbcons A Q) bb liftbb

-- equation 3 
-- 
-- equality GADT 
data Equal {l} : Set l → Set l → Set l where
  refl : ∀ {A : Set l} → Equal A A

Equal^ : ∀ {l} (A B : Set l) → (A → Set l) → (B → Set l) → (Equal A B → Set l)
Equal^ A .A Qa Qb refl = ∀ x → Equal (Qa x) (Qb x)

-- equation 4
data Seq : Set → Set₁ where
  const : ∀ {A : Set} → A → Seq A
  pair  : ∀ {A : Set} → ∀ (B C : Set) → Equal A (B × C) → Seq B → Seq C → Seq A

-- need to wrap (non-dependent) function type with this datatype
-- in order to pattern match on terms of type Equal (Arr A B) (Arr C D).
-- used in LType/LTerm
data Arr (A B : Set) : Set where
  arr : (A → B) → Arr A B

-- equation 5 
data LType : Set → Set₁ where
  bool : ∀ {A : Set} → ∀ (B : Set) → (e : Equal A Bool) → LType A
  arr  : ∀ {A : Set} → ∀ (B C : Set) → (e : Equal A (Arr B C)) → LType B → LType C → LType A
  list : ∀ {A : Set} → ∀ (B : Set) → (e : Equal A (List B)) → LType B → LType A

-- equation 6 
data LTerm : Set → Set₁ where
  var   : ∀ {A : Set} → (s : String) → (Ta : LType A) → LTerm A
  abs   : ∀ {A : Set} → ∀ (B C : Set) → (e : Equal A (Arr B C)) → (s : String) → (Tb : LType B) → (tc : LTerm C) → LTerm A
  app   : ∀ {A : Set} → ∀ (B : Set) → (tab : LTerm (Arr B A)) → (tb : LTerm B) → LTerm A
  list  : ∀ {A : Set} → ∀ (B : Set) → (e : Equal A (List B)) → List (LTerm B) → LTerm A

-- 4 . (Deep) induction for GADTs

-- equation 7
dIndEqual : ∀ (P : ∀ (A B : Set) → (A → Set) → (B → Set) → Equal A B → Set)
         → (∀ (C : Set) (Q Q' : C → Set) → Equal^ C C Q Q' refl → P C C Q Q' refl)
         → ∀ (A B : Set) (Qa : A → Set) (Qb : B → Set) (e : Equal A B) → Equal^ A B Qa Qb e → P A B Qa Qb e
dIndEqual P crefl A .A Qa Q'a  refl liftE = crefl A Qa Q'a liftE


K⊤ : ∀ {l} {A : Set l} → A → Set
K⊤ _ = ⊤

-- equation 8
indEqual : ∀ (Q : ∀ (A B : Set) → Equal A B → Set) → (∀ (C : Set) → Q C C refl)
            → ∀ (A B : Set) (e : Equal A B) → Q A B e
-- -- we can define indEqual as:
-- indEqual Q crefl A .A refl = crefl A

-- or we can define it in terms of the deep induction rule dIndEqual
indEqual Q srefl A B refl = dIndEqual P srefl' A B K⊤ K⊤ refl sliftE
  where P : ∀ (A B : Set) → (A → Set) → (B → Set) → Equal A B → Set
        P A B Qa Qb e = Q A B e
        srefl' : ∀ (C : Set) (Qc Q'c : C → Set) → Equal^ C C Qc Q'c refl → Q C C refl
        srefl' C Qc Q'c liftE' = srefl C
        sliftE : Equal^ A B K⊤ K⊤ refl
        sliftE a = refl


-- pair clause of Seq^ has type Set₁ because it quantifies over (B → Set) of type Set₁
-- so Seq^ must return an element of Set₁ in both cases
Seq^ : ∀ (A : Set) → (A → Set) → Seq A → Set₁
Seq^ A Qa (const a) = Lift _ (Qa a) -- need to use Lift to get into Set₁
Seq^ A Qa (pair B C e sb sc) =
  ∃[ Qb ] ∃[ Qc ] Equal^ A (B × C) Qa (Pair^ B C Qb Qc) e × Seq^ B Qb sb × Seq^ C Qc sc

-- 4.2 - (Deep) induction for Seq

-- equation 9 
dIndSeq : ∀ (P : ∀ (A : Set) → (A → Set) → Seq A → Set)
            → (∀ (A : Set) (Qa : A → Set) (a : A) → Qa a → P A Qa (const a))
            → (∀ (A B C : Set) (Qa : A → Set) (Qb : B → Set) (Qc : C → Set)
               (sb : Seq B) (sc : Seq C) (e : Equal A (B × C))
               → Equal^ A (B × C) Qa (Pair^ B C Qb Qc) e
               → P B Qb sb → P C Qc sc
               → P A Qa (pair B C e sb sc))
            → ∀ (A : Set) (Qa : A → Set) (sa : Seq A) → Seq^ A Qa sa → P A Qa sa
dIndSeq P cconst cpair A Qa (const a)            (lift liftA) = cconst A Qa a liftA
dIndSeq P cconst cpair A Qa (pair B C e sb sc) (Qb , Qc , liftE , liftB , liftC) =
  let pb : P B Qb sb
      pb = dIndSeq P cconst cpair B Qb sb liftB
      pc : P C Qc sc
      pc = dIndSeq P cconst cpair C Qc sc liftC
    in cpair A B C Qa Qb Qc sb sc e liftE pb pc


-- 4.3 - (Deep) induction for LTerm


-- define lifting of predicates for arrow type.
-- this is used to define LType^ and LTerm^
Arr^ : ∀ (A B : Set) → (A → Set) → (B → Set) → Arr A B → Set
Arr^ A B Qa Qb (arr f) = ∀ (a : A) → Qa a → Qb (f a)


-- Figure 1

LType^ : ∀ (A : Set) → (A → Set) → LType A → Set₁
-- use Σ-syntax as opposed to ∃-syntax in this clause since Qb is not used
-- and its type cannot be inferred (∃-syntax omits the type) 
-- -- LType^ A Qa (bool B e) = ∃[ Qb ] Equal^ A Bool Qa K⊤ e 
LType^ A Qa (bool B e) = Σ[ Qb ∈ (B → Set) ] Equal^ A Bool Qa K⊤ e
LType^ A Qa (arr B C e Tb Tc) =
  ∃[ Qb ] ∃[ Qc ] Equal^ A (Arr B C) Qa (Arr^ B C Qb Qc) e
                × LType^ B Qb Tb × LType^ C Qc Tc
LType^ A Qa (list B e Tb) =
  ∃[ Qb ] Equal^ A (List B) Qa (List^ B Qb) e × LType^ B Qb Tb


{-# TERMINATING #-}
LTerm^ : ∀ (A : Set) → (A → Set) → LTerm A → Set₁
LTerm^ A Qa (var s Ta) = LType^ A Qa Ta
LTerm^ A Qa (abs B C e s Tb tc) =
    ∃[ Qb ] ∃[ Qc ] Equal^ A (Arr B C) Qa (Arr^ B C Qb Qc) e
                   × LType^ B Qb Tb × LTerm^ C Qc tc
LTerm^ A Qa (app B tba tb) =
  ∃[ Qb ] LTerm^ (Arr B A) (Arr^ B A Qb Qa) tba × LTerm^ B Qb tb
LTerm^ A Qa (list B e ts) =
  ∃[ Qb ] Equal^ A (List B) Qa (List^ B Qb) e × List^ (LTerm B) (LTerm^ B Qb) ts

-- end Figure 1


-- equation 10 
{-# TERMINATING #-}
dIndLTerm : ∀ {l} (P : ∀ (A : Set) → (A → Set) → LTerm A → Set l)
                -- var
                → (∀ (A : Set) (Qa : A → Set) (s : String) (Ta : LType A)
                → LType^ A Qa Ta → P A Qa (var s Ta))
                -- abs
                → (∀ (A B C : Set) (Qa : A → Set) (Qb : B → Set) (Qc : C → Set)
                    (e : Equal A (Arr B C)) (s : String) (Tb : LType B) (tc : LTerm C)
                → Equal^ A (Arr B C) Qa (Arr^ B C Qb Qc) e
                → LType^ B Qb Tb → P C Qc tc → P A Qa (abs B C e s Tb tc))
                -- app
                → (∀ (A B : Set) (Qa : A → Set) (Qb : B → Set) (tba : LTerm (Arr B A)) (tb : LTerm B)
                    → P (Arr B A) (Arr^ B A Qb Qa) tba → P B Qb tb → P A Qa (app B tba tb))
                -- list
                → (∀ (A B : Set) (Qa : A → Set) (Qb : B → Set) (e : Equal A (List B)) (ts : List (LTerm B))
                    → Equal^ A (List B) Qa (List^ B Qb) e
                    → List^ (LTerm B) (P B Qb) ts
                → P A Qa (list B e ts))
                → ∀ (A : Set) (Qa : A → Set) (ta : LTerm A) → LTerm^ A Qa ta → P A Qa ta
dIndLTerm P cvar cabs capp clist A Qa (var s Ta) liftA = cvar A Qa s Ta liftA
dIndLTerm P cvar cabs capp clist A Qa (abs B C e s Tb tc) (Qb , Qc , liftE , liftTb , lifttc ) =
  cabs A B C Qa Qb Qc e s Tb tc liftE liftTb pc
    where pc  : P C Qc tc
          pc = (dIndLTerm P cvar cabs capp clist C Qc tc lifttc)

dIndLTerm P cvar cabs capp clist A Qa (app {A} B tba tb) (Qb , lifttba , lifttb) =
  capp A B Qa Qb tba tb pba pb
    where pba : P (Arr B A) (Arr^ B A Qb Qa) tba
          pba = dIndLTerm P cvar cabs capp clist (Arr B A) (Arr^ B A Qb Qa) tba lifttba
          pb : P B Qb tb
          pb = dIndLTerm P cvar  cabs capp clist B Qb tb lifttb


dIndLTerm {l} P cvar cabs capp clist A Qa (list B e ts) (Qb , liftE' , liftList) =
    let pts : PredMap (LTerm B) (LTerm^ B Qb) (P B Qb)
        pts  = dIndLTerm P cvar cabs capp clist B Qb
        plist : List^ (LTerm B) (P B Qb) ts
        plist = liftListMap (LTerm B) (LTerm^ B Qb) (P B Qb) pts ts liftList
    in clist A B Qa Qb e ts liftE' plist



----------------------------------------------------
-- 7 . Case Study : Extracting Types of Lambda Terms
----------------------------------------------------

-- postulates that liftings of K⊤ are extensionally equal to K⊤ for ADTs (Arr and List)
postulate
  Equal^ArrK⊤ : ∀ {A B C : Set} → (e : Equal A (Arr B C)) → Equal^ A (Arr B C) K⊤ (Arr^ B C K⊤ K⊤) e

  Equal^ListK⊤ : ∀ {A B : Set} → (e : Equal A (List B)) → Equal^ A (List B) K⊤ (List^ B K⊤) e


-- We also postulate function extensionality for predicates (i.e., functions whose codomains are sorts), which is needed to define Arr^EqualMap. 
Extensionality : (a b : Level) → Set _
Extensionality a b =
  {A : Set a} {f g : A → Set b} → (∀ x → Equal (f x) (g x)) → Equal (∀ z → f z) (∀ z → g z)

-- Note: this is an usual way to state extensionality. Normally we would expect function extensionality to be stated as:
--        (∀ x → Equal (f x) (g x)) → Equal f g 
-- but our Equal GADT can only compare types (e.g., elements of Set, Set₁, etc.), not arbitrary terms f, g : A → Set b, meaning that Equal f g is not well-typed. 
-- We could resort to using Agda's propositional equality _≡_ to give the normal statement of extensionality,
-- from which the following statement follows (because if f and g are equal, (∀ z → f z) and (∀ z → g z) are equal too).
-- But for simplicity of presentation (primarily to avoid going back and forth between _≡_ and Equal), we directly postulate the term needed to define Arr^EqualMap:
postulate
  extensionality : ∀ {a b} → Extensionality a b

ext-refl : ∀ {a b} {A : Set a} → (f : A → Set b) → ∀ x → Equal (f x) (f x)
ext-refl f x = refl

cong₂ : ∀ {l} {A B C D : Set l} → (F : Set l → Set l → Set l) → Equal A B → Equal C D → Equal (F A C) (F B D)
cong₂ F refl refl = refl

sym : ∀ {l} {A B : Set l} → Equal A B → Equal B A
sym refl = refl

trans : ∀ {l} {A B C : Set l} → Equal A B → Equal B C → Equal A C
trans refl p = p

-- gives extensional proof of equality between Arr^ Qa Qb f and Arr^ Qa' Qb' f
Arr^EqualMap' : ∀ {A B : Set} → (Qa Qa' : A → Set) → (Qb Qb' : B → Set)
          → (extA : ∀ x → Equal (Qa x) (Qa' x))
          → (extB : ∀ x → Equal (Qb x) (Qb' x))
          → (f : A → B)
          → ∀ (z : A) → Equal (Qa z → Qb (f z)) (Qa' z → Qb' (f z))
Arr^EqualMap' {A} {B} Qa Qa' Qb Qb' extA extB f z = cong₂ (λ (X Y : Set) → X → Y) (extA z) (extB (f z))

-- use extensionality postulate to turn Arr^EqualMap' into intensional proof of equality between Arr^ Qa Qb f and Arr^ Qa' Qb' f
Arr^EqualMap : ∀ {A B : Set} → (Qa Qa' : A → Set) → (Qb Qb' : B → Set)
          → (extA : ∀ x → Equal (Qa x) (Qa' x))
          → (extB : ∀ x → Equal (Qb x) (Qb' x))
          → (f : Arr A B)
          → Equal (Arr^ A B Qa Qb f) (Arr^ A B Qa' Qb' f)
Arr^EqualMap {A} {B} Qa Qa' Qb Qb' extA extB (arr f) = extensionality (Arr^EqualMap' Qa Qa' Qb Qb' extA extB f)


-- if two predicates Qa and Qa' are extensionally equal, we can make morphism of predicates from LType^ A Qa to LType^ A Qa'
LType^EqualMap : ∀ {A : Set} → (Qa Qa' : A → Set) → (ext : ∀ x → Equal (Qa x) (Qa' x)) → PredMap (LType A) (LType^ A Qa) (LType^ A Qa')
LType^EqualMap Qa Qa' ext (bool B refl) (Qb , liftE) = Qb , (λ x → trans (sym (ext x)) (liftE x))
LType^EqualMap Qa Qa' ext (arr B C refl Tb Tc) (Qb , Qc , liftE , liftTb , liftTc) = Qb , Qc , ((λ x → trans (sym (ext x)) (liftE x)) , liftTb , liftTc)
LType^EqualMap Qa Qa' ext (list B refl Ta) (Qb , liftE , liftTb) =  Qb , (λ x → trans (sym (ext x)) (liftE x)) , liftTb


-- if two predicates Qa and Qa' are extensionally equal, we can make morphism of predicates from LTerm^ A Qa to LTerm^ A Qa'
LTerm^EqualMap : ∀ {A : Set} → (Qa Qa' : A → Set) → (ext : Equal^ A A Qa Qa' refl) → PredMap (LTerm A) (LTerm^ A Qa) (LTerm^ A Qa')
LTerm^EqualMap Qa Qa' ext (var s Ta) LLTy^Qa = LType^EqualMap Qa Qa' ext Ta LLTy^Qa
LTerm^EqualMap Qa Qa' ext (abs B C refl s Tb tc) (Qb , Qc , Equal^Arr , liftTb , lifttc) =
  Qb , Qc , (((λ x → trans (sym (ext x)) (Equal^Arr x))) , liftTb , lifttc)
--
-- need to use LTerm^EqualMap to get proof of:
--                  LTerm^ (Arr B C) (Arr^ B C Qb Qa') tba
-- from term of type LTerm^ (Arr B C) (Arr^ B C Qb Pa) tba
--
-- but to use LTerm^EqualMap in this scenario we need
-- ext : ∀ f → Equal (Arr^ B C Qb Qa f) (Arr^ B C Qb Qa' f)
--
-- which means we need a term Arr^EqualMap
-- that takes extensionally equal predicates and gives an extensional proof of equality on
-- the lifted predicates (Arr^ B C Qb Qa x) and (Arr^ B C Qb Qa' x)
LTerm^EqualMap Qa Qa' ext (app {A} B tba tb) (Qb , lifttba , lifttb) =
  Qb , LTerm^EqualMap (Arr^ B A Qb Qa) (Arr^ B A Qb Qa') ext' tba lifttba , lifttb 
  where ext' : ∀ (f : Arr B A) → Equal (Arr^ B A Qb Qa f) (Arr^ B A Qb Qa' f)
        ext' = Arr^EqualMap Qb Qb Qa Qa' (ext-refl Qb) ext
LTerm^EqualMap Qa Qa' ext (list B refl ts) (Qb , liftE , liftts ) = Qb , ((λ x → trans (sym (ext x)) (liftE x)) , liftts)


-- List^ A K⊤ is always inhabited for any list xs 
List^K⊤ : ∀ {l} (A : Set l) (xs : List A) → List^ A K⊤ xs
List^K⊤ A nil = lift tt
List^K⊤ A (cons x xs) = tt , List^K⊤ A xs

-- LType^ A K⊤ is always inhabited for any (Ta : LType A) 
LType^K⊤ : ∀ (A : Set) → (Ta : LType A) → LType^ A K⊤ Ta
LType^K⊤ A (bool B refl) = K⊤ , λ x → refl
LType^K⊤ .(Arr B C) (arr B C refl Tb Tc) = K⊤ , K⊤ , Equal^ArrK⊤  refl , LType^K⊤ B Tb , LType^K⊤ C Tc
LType^K⊤ A (list B refl Ta) = K⊤ , Equal^ListK⊤ refl , LType^K⊤ B Ta

-- LTerm^ A K⊤ is always inhabited for any (t : LTerm A) 
{-# TERMINATING #-}
LTerm^K⊤ : ∀ (A : Set) → (t : LTerm A) → LTerm^ A K⊤ t
LTerm^K⊤ A (var s Ta) = LType^K⊤ A Ta
LTerm^K⊤ A (abs B C e s T t') =
  K⊤ , K⊤ , Equal^ArrK⊤ e , LType^K⊤ B T , LTerm^K⊤ C t'

-- need proof LTerm^Arr : LTerm^ (Arr A B) (Arr^ A B K⊤ K⊤) t1
-- we can produce it given
-- - LTerm^ (Arr A B) K⊤ t1 (which we get by recursion), and 
-- - proof of extensional equality for (Arr^ A B K⊤ K⊤) and K⊤ (postulated), and 
-- - LTerm^EqualMap, which takes extensionally equal predicates Q1 and Q2 and gives a map from (LTerm^ A Q1) to (LTerm^ A Q2)
LTerm^K⊤ A (app {A} B t1 t2) =
    K⊤ , LTerm^Arr , LTerm^K⊤ B t2
  where LK⊤ : LTerm^ (Arr B A) K⊤ t1
        LK⊤ = LTerm^K⊤ (Arr B A) t1
        LTerm^Arr : LTerm^ (Arr B A) (Arr^ B A K⊤ K⊤) t1
        LTerm^Arr = LTerm^EqualMap K⊤ (Arr^ B A K⊤ K⊤) (Equal^ArrK⊤ refl) t1 LK⊤

LTerm^K⊤ A (list B e ts) =
    K⊤ , Equal^ListK⊤ e , LList^LTerm^K⊤
    where mK⊤ : PredMap (LTerm B) K⊤ (LTerm^ B K⊤)
          mK⊤ t' tt = LTerm^K⊤ B t'
          LList^LTerm^K⊤ : List^ (LTerm B) (LTerm^ B K⊤) ts
          LList^LTerm^K⊤ = liftListMap (LTerm B) K⊤ (LTerm^ B K⊤) mK⊤ ts (List^K⊤ (LTerm B) ts)




-------------------------------------------------------
-- type inference example
-------------------------------------------------------

-- GetType predicate is used to represent type inference
-- where the type inferred for (t : LTerm A) is either
-- - just Ta , where Ta : LType A
-- - nothing , representing failure of type inference 
GetType : ∀ (A : Set) → (t : LTerm A) → Set₁
GetType A t = Maybe (LType A)


cvar : ∀ (A : Set) (Qa : A → Set) (s : String) (Ta : LType A) → LType^ A Qa Ta → Maybe (LType A)
cvar _ _ _ Ta _ = just Ta

cabs : ∀ (A B C : Set) → (Qa : A → Set) (Qb : B → Set) (Qc : C → Set) (e : Equal A (Arr B C))
       → (s : String) (Tb : LType B) (tc : LTerm C)
       → Equal^ A (Arr B C) Qa (Arr^ B C Qb Qc) e
       → LType^ B Qb Tb
       → Maybe (LType C)
       → Maybe (LType A)
cabs A B C Qa Qb Qc e s Tb tc liftE liftTb nothing = nothing
cabs A B C Qa Qb Qc e s Tb tc liftE liftTb (just Tc) = just (arr B C e Tb Tc)


capp : ∀  (A B : Set) (Qa : A → Set) (Qb : B → Set) (tba : LTerm (Arr B A)) (tb : LTerm B)
       → Maybe (LType (Arr B A)) → Maybe (LType B)
       → Maybe (LType A)
capp A B Qa Qb tba ta  nothing ma = nothing
capp A B Qa Qb tba ta (just (bool C e))            mb = nothing -- impossible case - e : Equal (Arr A B) Bool
-- injective-type-constructors option used in the 
-- following case to match on refl : Equal (Arr B A) (Arr B A)
capp A B Qa Qb tba ta (just (arr .B .A refl Tb Ta)) mb = just Ta
capp A B Qa Qb tba ta (just (list C e ts))         mb = nothing -- impossible case - e : Equal (Arr A B) (List C)


clist : ∀ (A B : Set) (Qa : A → Set) (Qb : B → Set) (e : Equal A (List B)) (ts : List (LTerm B))
        → Equal^ A (List B) Qa (List^ B Qb) e
        → List^ (LTerm B) (GetType B) ts
        → Maybe (LType A)
-- empty list of terms, so cannot infer an STLC type
clist A B Qa Qb e nil liftE liftts = nothing
-- otherwise use first element of List^ (LTerm B) (GetType B) ts
clist A B Qa Qb e (cons t ts') liftE (nothing , liftts') = nothing
clist A B Qa Qb e (cons t ts') liftE (just T' , liftts') = just (list B e T')


getTypeProof : ∀ (A : Set) → (t : LTerm A) → GetType A t
getTypeProof A t = dIndLTerm (λ A Qa → GetType A) cvar cabs capp clist A K⊤ t (LTerm^K⊤ A t)


------------------------------------------------
-- example lambda terms and their inferred types 
------------------------------------------------

TB : LType Bool
TB = bool Bool refl

-- test term of type Bool - single variable x : Bool 
test1 : LTerm Bool
test1 = var "x" TB
test1-type : Maybe (LType Bool)
test1-type = getTypeProof Bool test1
-- = just (bool Bool refl)

-- test abstraction term  - λ x . x 
test2 : LTerm (Arr Bool Bool)
test2 = abs Bool Bool refl "x" TB test1
test2-type : Maybe (LType (Arr Bool Bool))
test2-type = getTypeProof (Arr Bool Bool) test2
-- = just (arr Bool Bool refl TB TB)

-- test application term - (λ x . x) x
test3 : LTerm Bool
test3 = app Bool test2 test1 
test3-type : Maybe (LType Bool)
test3-type = getTypeProof Bool test3
-- = just (bool Bool refl) 

-- test term of list type - singleton list [ x ]
test4 : LTerm (List Bool)
test4 = list Bool refl (cons test1 nil)
test4-type : Maybe (LType (List Bool))
test4-type = getTypeProof (List Bool) test4
-- = just (list Bool refl (bool Bool refl))

-- test (empty list) term of list type 
-- getTypeProof returns nothing in this case, indicating that no type can be inferred for the empty list term 
test5 : LTerm (List Bool)
test5 = list Bool refl nil
test5-type : Maybe (LType (List Bool))
test5-type = getTypeProof (List Bool) test5
-- = nothing
