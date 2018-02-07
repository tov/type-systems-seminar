module _ where

open import Data.Nat
  using (ℕ ; _≟_ ; suc ; zero ;
         _+_ ; _≤_ ; _≤′_ ; _<′_ ;
         z≤n ; s≤s ; ≤′-refl)
open import Data.Nat.Properties
  using (s≤′s ; z≤′n ; ≤′⇒≤ ; ≤⇒≤′ ; n≤1+n ; ≤-step)
open import Data.Nat.Properties.Simple
  using (+-comm ; +-assoc ; +-suc)
open import Relation.Nullary
  using (yes ; no ; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; cong ; trans)
open import Data.List
  using (List ; _∷_ ; [])
open import Data.Product
  using (_,_ ; _,′_ ; _×_ ; proj₁ ; proj₂ ; ∃ ; Σ-syntax)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Induction.Lexicographic
  using ([_⊗_])
open import Data.Unit
  using (⊤ ; tt)
open import Induction.Nat as N
open import Relation.Binary using (Rel)
open import Induction
open import Induction.Nat
open import Induction.WellFounded

data letzl : Set where
  nat  : (n : ℕ) -> letzl
  nil  : letzl
  cons : (car : letzl) -> (cdr : letzl) -> letzl
  add  : (lhs : letzl) -> (rhs : letzl) -> letzl
  car  : (pr : letzl) -> letzl
  cdr  : (pr : letzl) -> letzl
  var  : (n : ℕ) -> letzl
  bind : (n : ℕ) -> (rhs : letzl) -> (body : letzl) -> letzl

data val : letzl -> Set where
  natval : (n : ℕ) -> val (nat n)
  nilval : val nil
  consval : ∀ hd tl -> (hdval : val hd) -> (tlval : val tl) -> val (cons hd tl)

subst : ∀ (d : ℕ) ->  (e : letzl) -> ∀ {v : letzl} -> val v -> letzl
subst d (nat n) v₁ = nat n
subst d nil v₁ = nil
subst d (cons e e₁) v₁ = cons (subst d e v₁) (subst d e₁ v₁)
subst d (add e e₁) v₁ = add (subst d e v₁) (subst d e₁ v₁)
subst d (car e) v₁ = car (subst d e v₁)
subst d (cdr e) v₁ = cdr (subst d e v₁)
subst d (var n) v₁ with n ≟ d
subst d (var n) {v} v₁ | yes p = v
subst d (var n) v₁ | no ¬p = var n
subst d (bind n e e₁) v₁ with n ≟ d
subst d (bind n e e₁) v₁ | yes p = bind n (subst d e v₁) e₁
subst d (bind n e e₁) v₁ | no ¬p = bind n (subst d e v₁) (subst d e₁ v₁)

data Config : Set where
  WRONG : Config
  eC : (e : letzl) -> Config

data finishedConfig : Config -> Set where
  finWRONG : finishedConfig WRONG
  finVal : ∀ {v} -> val v -> finishedConfig (eC v)

data Ectxt : Set where
  hole : Ectxt
  Econsl : (car : Ectxt) -> (cdr : letzl) -> Ectxt
  Econsr : (car : letzl) -> val car -> (cdr : Ectxt) -> Ectxt
  E+l : (lhs : Ectxt) -> (rhs : letzl) -> Ectxt
  E+r : (lhs : letzl) -> val lhs -> (rhs : Ectxt) -> Ectxt
  Ecar : (arg : Ectxt) -> Ectxt
  Ecdr : (arg : Ectxt) -> Ectxt
  Ebind : (x : ℕ) -> (rhs : Ectxt) -> (body : letzl) -> Ectxt

data decomp : letzl -> Ectxt -> letzl -> Set where
  Dhole  : ∀ e -> decomp e hole e
  Dconsl : ∀ {E e eo ei} ->
    decomp eo E ei ->
    decomp (cons eo e) (Econsl E e) ei
  Dconsr : ∀ {E v eo ei} -> (vval : val v) ->
    decomp eo E ei ->
    decomp (cons v eo) (Econsr v vval E) ei
  D+l    : ∀ {E e eo ei} ->
    decomp eo E ei ->
    decomp (add eo e) (E+l E e) ei
  D+r    : ∀ {E v eo ei} -> (vval : val v) ->
    decomp eo E ei ->
    decomp (add v eo) (E+r v vval E) ei
  Dcar   : ∀ {E eo ei} ->
    decomp eo E ei ->
    decomp (car eo) (Ecar E) ei
  Dcdr   : ∀ {E eo ei} ->
    decomp eo E ei ->
    decomp (cdr eo) (Ecdr E) ei
  Dbind  : ∀ {E eo ei x e} ->
    decomp eo E ei ->
    decomp (bind x eo e) (Ebind x E e) ei

plug : Ectxt -> letzl -> letzl
plug hole e = e
plug (Econsl E cdr₁) e = cons (plug E e) cdr₁
plug (Econsr car₁ x E) e = cons car₁ (plug E e)
plug (E+l E rhs) e = add (plug E e) rhs
plug (E+r lhs x E) e = add lhs (plug E e)
plug (Ecar E) e = car (plug E e)
plug (Ecdr E) e = cdr (plug E e)
plug (Ebind x E body) e = bind x (plug E e) body

plugeq : ∀ {e E e₂} ->
  decomp e E e₂ ->
  e ≡ plug E e₂
plugeq (Dhole e) = refl
plugeq (Dconsl edc) =
 cong (λ x → cons x _) (plugeq edc)
plugeq (Dconsr vval edc) =
 cong (λ x → cons _ x) (plugeq edc)
plugeq (D+l edc) =
 cong (λ x → add x _) (plugeq edc)
plugeq (D+r vval edc) =
 cong (λ x → add _ x) (plugeq edc)
plugeq (Dcar edc) =
 cong car (plugeq edc)
plugeq (Dcdr edc) =
 cong cdr (plugeq edc)
plugeq (Dbind edc) =
 cong (λ x → bind _ x _) (plugeq edc)

data step : letzl -> Config -> Set where
  Sadd : ∀ {n₁ n₂ e₁ e₂ E} ->
     decomp e₁ E (add (nat n₁) (nat n₂)) ->
     decomp e₂ E (nat (n₁ + n₂)) ->
     step e₁ (eC e₂)
  Scar : ∀ {v₁ v₂ e₁ e₂ E} -> val v₁ -> val v₂ ->
    decomp e₁ E (car (cons v₁ v₂)) ->
    decomp e₂ E v₁ ->
    step e₁ (eC e₂)
  Scdr : ∀ {v₁ v₂ e₁ e₂ E} -> val v₁ -> val v₂ ->
    decomp e₁ E (cdr (cons v₁ v₂)) ->
    decomp e₂ E v₂ ->
    step e₁ (eC e₂)
  Sbind : ∀ {x v e e₁ e₂ E} -> (valv : val v) ->
    decomp e₁ E (bind x v e) ->
    decomp e₂ E (subst x e valv) ->
    step e₁ (eC e₂)
  Scarnil : ∀ {e₁ E} ->
    decomp e₁ E (car nil) ->
    step e₁ WRONG
  Scdrnil : ∀ {e₁ E} ->
    decomp e₁ E (cdr nil) ->
    step e₁ WRONG

∥_∥ : letzl -> ℕ
∥ nat n ∥ = 0
∥ nil ∥ = 0
∥ cons e e₁ ∥ = ∥ e ∥ + ∥ e₁ ∥
∥ add e e₁ ∥ = 1 + ∥ e ∥ + ∥ e₁ ∥
∥ car e ∥ = 1 + ∥ e ∥
∥ cdr e ∥ = 1 + ∥ e ∥
∥ var n ∥ = 0
∥ bind x e e₁ ∥ =  1 + ∥ e ∥ + ∥ e₁ ∥

values-have-size-0 : ∀ {v} -> val v -> ∥ v ∥ ≡ 0
values-have-size-0 (natval n) = refl
values-have-size-0 nilval = refl
values-have-size-0 (consval hd tl v v₁)
 rewrite values-have-size-0 v | values-have-size-0 v₁
 = refl

subst-preserves-size : ∀ {v} -> ∀ x e ->
  (valv : val v) ->
  ∥ subst x e valv ∥ ≡ ∥ e ∥
subst-preserves-size x (nat n) valv = refl
subst-preserves-size x nil valv = refl
subst-preserves-size x (cons e e₁) valv
  rewrite subst-preserves-size x e valv
        | subst-preserves-size x e₁ valv
  = refl
subst-preserves-size x (add e e₁) valv
  rewrite subst-preserves-size x e valv
        | subst-preserves-size x e₁ valv
  = refl
subst-preserves-size x (car e) valv
  rewrite subst-preserves-size x e valv
  = refl
subst-preserves-size x (cdr e) valv
  rewrite subst-preserves-size x e valv
  = refl
subst-preserves-size x (var n) valv
  with n ≟ x
... | yes p = values-have-size-0 valv
... | no ¬p = refl
subst-preserves-size x (bind n e e₁) valv
  with n ≟ x
... | yes p
  rewrite subst-preserves-size x e valv
  = refl
... | no ¬p
  rewrite subst-preserves-size x e valv
        | subst-preserves-size x e₁ valv
  = refl

data type : Set where
  NatT : type
  ListT : type

data lookup : List (ℕ × type) -> ℕ -> type -> Set where
  Lhere : ∀ {n t l} ->
    lookup ((n , t) ∷ l) n t
  Lcont : ∀ {t t′ l n m} ->
   lookup l n t ->
   (¬x≡y : ¬ (m ≡ n)) ->
   lookup ((m , t′) ∷ l) n t

data tc : List (ℕ × type) -> letzl -> type -> Set where
  tnat : ∀ {env n} -> tc env (nat n) NatT
  tnil : ∀ {env} -> tc env nil ListT
  tadd : ∀ {env e1 e2} ->
    tc env e1 NatT ->
    tc env e2 NatT ->
    tc env (add e1 e2) NatT
  tcons : ∀ {env e1 e2} ->
    tc env e1 NatT ->
    tc env e2 ListT ->
    tc env (cons e1 e2) ListT
  tcar : ∀ {env e} ->
    tc env e ListT ->
    tc env (car e) NatT
  tcdr : ∀ {env e} ->
    tc env e ListT ->
    tc env (cdr e) ListT
  tx : ∀ {env n t} ->
    lookup env n t ->
    tc env (var n) t
  tbind : ∀ {x env e₁ e₂ τ₁ τ₂} ->
    tc env e₁ τ₁ ->
    tc ((x , τ₁) ∷ env) e₂ τ₂ ->
    tc env (bind x e₁ e₂) τ₂

replacement : ∀ {e E e₁ e₂ τ} ->
  decomp e E e₁ ->
  tc [] e τ ->
  ∃ (\ { τₑ ->
    tc [] e₁ τₑ ×
    (tc [] e₂ τₑ ->
     tc [] (plug E e₂) τ) })
replacement (Dhole e) tce = _ , tce , (λ x → x)
replacement (Dconsl dc) (tcons tce tce₁)
  with replacement dc tce
... | _ , tc , f
  = _ , tc , (λ x → tcons (f x) tce₁)
replacement (Dconsr vval dc) (tcons tce tce₁)
  with replacement dc tce₁
... | _ , tc , f
  = _ , tc , (λ x → tcons tce (f x))
replacement (D+l dc) (tadd tce tce₁)
  with replacement dc tce
... | _ , tc , f
  = _ , tc , (λ x → tadd (f x) tce₁)
replacement (D+r vval dc) (tadd tce tce₁)
  with replacement dc tce₁
... | _ , tc , f
  = _ , tc , (λ x → tadd tce (f x))
replacement (Dcar dc) (tcar tce)
  with replacement dc tce
... | _ , tc , f
  = _ , tc , (λ x → tcar (f x))
replacement (Dcdr dc) (tcdr tce)
  with replacement dc tce
... | _ , tc , f
  = _ , tc , (λ x → tcdr (f x))
replacement (Dbind dc) (tbind tce tce₁)
  with replacement dc tce
... | _ , tc , f
  = _ , tc , (λ x → tbind (f x) tce₁)

values-no-vars : ∀ {env env' v τ} ->
  val v ->
  tc env v τ ->
  tc env' v τ
values-no-vars (natval n) tnat = tnat
values-no-vars nilval tnil = tnil
values-no-vars (consval hd tl valv valv₁) (tcons tcv tcv₁)
  = tcons (values-no-vars valv tcv) (values-no-vars valv₁ tcv₁)

data sameenv : List (ℕ × type) -> List (ℕ × type) -> Set where
  mtsame : sameenv [] []
  cosame : ∀ {env1 env2 x τ} ->
    sameenv env1 env2 ->
    sameenv ((x , τ) ∷ env1) ((x , τ) ∷ env2)
  exsame : ∀ {x y τx τy env1 env2} ->
    sameenv env1 env2 ->
    (¬x≡y : ¬ (x ≡ y)) ->
    sameenv ((x , τx) ∷ (y , τy) ∷ env1)
            ((y , τy) ∷ (x , τx) ∷ env2)
  resame : ∀ {x τx τignored env1 env2} ->
    sameenv env1 env2 ->
    sameenv ((x , τx) ∷ (x , τignored) ∷ env1)
            ((x , τx) ∷ env2)

sasame : ∀ {env} -> sameenv env env
sasame {[]} = mtsame
sasame {x ∷ env} = cosame (sasame {env})

samelookup : ∀ {env1 env2 n t} ->
  sameenv env1 env2 ->
  lookup env1 n t ->
  lookup env2 n t
samelookup mtsame l = l
samelookup (cosame se) Lhere = Lhere
samelookup (cosame se) (Lcont l ¬x≡y)
  = Lcont (samelookup se l) ¬x≡y
samelookup (exsame se ¬x≡y) Lhere
  = Lcont Lhere (λ y≡x → ¬x≡y (sym y≡x))
samelookup (exsame se ¬x≡y₁) (Lcont Lhere ¬x≡y₂) = Lhere
samelookup (exsame se ¬x≡y₁) (Lcont (Lcont l ¬x≡y) ¬x≡y₂)
  = Lcont (Lcont (samelookup se l) ¬x≡y₂) ¬x≡y
samelookup (resame se) Lhere = Lhere
samelookup (resame se) (Lcont Lhere ¬x≡y) = ⊥-elim (¬x≡y refl)
samelookup (resame se) (Lcont (Lcont l ¬x≡y) ¬x≡y₁)
  = Lcont (samelookup se l) ¬x≡y

sametc : ∀ {env1 env2 e τ} ->
  sameenv env1 env2 ->
  tc env1 e τ ->
  tc env2 e τ
sametc se tnat = tnat
sametc se tnil = tnil
sametc se (tadd tc₁ tc₂)
 = tadd (sametc se tc₁) (sametc se tc₂)
sametc se (tcons tc₁ tc₂)
 = tcons (sametc se tc₁) (sametc se tc₂)
sametc se (tcar tc₁) = tcar (sametc se tc₁)
sametc se (tcdr tc₁) = tcdr (sametc se tc₁)
sametc se (tx x) = tx (samelookup se x)
sametc se (tbind tc₁ tc₂)
  = tbind (sametc se tc₁) (sametc (cosame se) tc₂)

exchange : ∀ {env x y τx τy e τ} -> ¬ (x ≡ y) ->
  tc ((x , τx) ∷ (y , τy) ∷ env) e τ ->
  tc ((y , τy) ∷ (x , τx) ∷ env) e τ
exchange ¬x≡y tc = sametc (exsame sasame ¬x≡y) tc

redundant : ∀ {x env τx τignored e τ} ->
  tc ((x , τx) ∷ (x , τignored) ∷ env) e τ ->
  tc ((x , τx) ∷ env) e τ
redundant tc = sametc (resame sasame) tc

substitution : ∀ {x τₓ env e τ v}  ->
  (valv : val v) ->
  tc ((x , τₓ) ∷ env) e τ ->
  tc env v τₓ ->
  tc env (subst x e valv) τ
substitution = thm where
  thm : ∀ {x τₓ env e τ v}  ->
    (valv : val v) ->
    tc ((x , τₓ) ∷ env) e τ ->
    tc env v τₓ ->
    tc env (subst x e valv) τ
  thm valv tnat vderiv = tnat
  thm valv tnil vderiv = tnil
  thm valv (tadd ederiv ederiv₁) vderiv =
    tadd (thm valv ederiv vderiv)
         (thm valv ederiv₁ vderiv)
  thm valv (tcons ederiv ederiv₁) vderiv =
    tcons (thm valv ederiv vderiv)
          (thm valv ederiv₁ vderiv)
  thm valv (tcar ederiv) vderiv =
    tcar (thm valv ederiv vderiv)
  thm valv (tcdr ederiv) vderiv =
    tcdr (thm valv ederiv vderiv)

  thm{y} valv (tx{_}{x} x₁) vderiv
    with x ≟ y
  thm {x} valv (tx Lhere) vderiv
    | yes p = vderiv
  thm {x} valv (tx {_} {n} (Lcont x₁ x₂)) vderiv
    | yes p = ⊥-elim (x₂ (sym p))
  thm {x} valv (tx Lhere) vderiv
    | no ¬p = ⊥-elim (¬p refl)
  thm {x} valv (tx {_} {n} (Lcont x₁ x₂)) vderiv
    | no ¬p = tx x₁

  thm {y} valv (tbind {x} rhsderiv bodyderiv) vderiv
    with x ≟ y
  ... | no ¬p =
    tbind
     (thm valv rhsderiv vderiv)
     (thm valv
          (exchange ¬p bodyderiv)
          (values-no-vars valv vderiv))
  ... | yes p rewrite p =
    tbind
      (thm valv rhsderiv vderiv)
      (redundant bodyderiv)

preservation : ∀ {e₁ e₂ τ} ->
  (tc [] e₁ τ) ->
  (step e₁ (eC e₂)) ->
  (tc [] e₂ τ)
preservation tce (Sadd{n₁}{n₂} dc1 dc2)
  with replacement dc1 tce
... | NatT , tadd tcadd tcadd₁ , f
  with f (tnat {n = n₁ + n₂})
... | tcplug rewrite plugeq dc2
  = tcplug
preservation tce (Scar valv₁ valv₂ dc1 dc2)
  with replacement dc1 tce
... | NatT , tcar (tcons tccar tccdr) , f
  with f tccar
... | tcplug rewrite plugeq dc2
  = tcplug
preservation tce (Scdr valv₁ valv₂ dc1 dc2)
  with replacement dc1 tce
... | carty , tcdr (tcons tccar tccdr) , f
  with f tccdr
... | tcplug rewrite plugeq dc2
  = tcplug
preservation tce (Sbind valv dc1 dc2)
  with replacement dc1 tce
... | t , tbind trhs tbody , f
  with substitution valv tbody trhs
... | tsubst
  with f tsubst
... | tplug rewrite plugeq dc2
  = tplug

concat : Ectxt -> Ectxt -> Ectxt
concat hole E₂ = E₂
concat (Econsl E₁ cdr₁) E₂ = Econsl (concat E₁ E₂) cdr₁
concat (Econsr car₁ x E₁) E₂ = Econsr car₁ x (concat E₁ E₂)
concat (E+l E₁ rhs) E₂ = E+l (concat E₁ E₂) rhs
concat (E+r lhs x E₁) E₂ = E+r lhs x (concat E₁ E₂)
concat (Ecar E₁) E₂ = Ecar (concat E₁ E₂)
concat (Ecdr E₁) E₂ = Ecdr (concat E₁ E₂)
concat (Ebind x E₁ body) E₂ = Ebind x (concat E₁ E₂) body

addctxt : ∀ {e₁ E e₂} -> ∀ E₂ ->
  decomp e₁ E e₂ ->
  decomp (plug E₂ e₁) (concat E₂ E) e₂
addctxt hole dc = dc
addctxt (Econsl E₂ cdr₁) dc = Dconsl (addctxt E₂ dc)
addctxt (Econsr car₁ x E₂) dc = Dconsr x (addctxt E₂ dc)
addctxt (E+l E₂ rhs) dc = D+l (addctxt E₂ dc)
addctxt (E+r lhs x E₂) dc = D+r x (addctxt E₂ dc)
addctxt (Ecar E₂) dc = Dcar (addctxt E₂ dc)
addctxt (Ecdr E₂) dc = Dcdr (addctxt E₂ dc)
addctxt (Ebind x E₂ body) dc = Dbind (addctxt E₂ dc)

stepEnoerr : ∀ {e e′} -> ∀ E -> step e (eC e′) -> step (plug E e) (eC (plug E e′))
stepEnoerr E (Sadd x x₁) = Sadd (addctxt E x) (addctxt E x₁)
stepEnoerr E (Scar x x₁ x₂ x₃) = Scar x x₁ (addctxt E x₂) (addctxt E x₃)
stepEnoerr E (Scdr x x₁ x₂ x₃) = Scdr x x₁ (addctxt E x₂) (addctxt E x₃)
stepEnoerr E (Sbind valv x₁ x₂) = Sbind valv (addctxt E x₁) (addctxt E x₂)

stepEerr : ∀ {e} -> ∀ E -> step e WRONG -> step (plug E e) WRONG
stepEerr E (Scarnil x) = Scarnil (addctxt E x)
stepEerr E (Scdrnil x) = Scdrnil (addctxt E x)

stepE : ∀ {e c} -> ∀ E -> step e c -> ∃ \ c′ -> step (plug E e) c′
stepE {e} {WRONG} E stepec = WRONG , stepEerr E stepec
stepE {e} {eC e₁} E stepec = eC (plug E e₁) , stepEnoerr E stepec


progress : ∀ {e τ} ->
  tc [] e τ ->
  ∃ (\ e′ -> step e e′) ⊎ val e

progress tnat = inj₂ (natval _)

progress tnil = inj₂ nilval

progress (tcons tc₁ tc₂) with progress tc₁
progress (tcons tc₁ tc₂) | inj₁ (e′ , stepee′)
  = inj₁ (stepE (Econsl hole _) stepee′)
progress (tcons tc₁ tc₂) | inj₂ vale1 with progress tc₂
progress (tcons tc₁ tc₂) | inj₂ vale1 | (inj₁ (e′ , stepee′))
  = inj₁ (stepE (Econsr _ vale1 hole) stepee′)
progress (tcons tc₁ tc₂) | inj₂ vale1 | (inj₂ vale2)
  = inj₂ (consval _ _ vale1 vale2)

progress (tadd tc₁ tc₂) with progress tc₁
progress (tadd tc₁ tc₂) | inj₁ (e′ , stepee′)
  = inj₁ (stepE (E+l hole _) stepee′)
progress (tadd tc₁ tc₂) | inj₂ vale1 with progress tc₂
progress (tadd tc₁ tc₂) | inj₂ vale1 | inj₁ (e′ , stepee′)
  = inj₁ (stepE (E+r _ vale1 hole) stepee′)
progress (tadd tc₁ tc₂) | inj₂ (natval n₁) | (inj₂ (natval n₂))
  = inj₁ (_ , Sadd (Dhole _) (Dhole _))
progress (tadd tc₁ ()) | inj₂ (natval n) | (inj₂ nilval)
progress (tadd tc₁ ()) | inj₂ (natval n) | (inj₂ (consval hd tl vale2 vale3))
progress (tadd () tc₂) | inj₂ nilval | (inj₂ vale2)
progress (tadd () tc₂) | inj₂ (consval hd tl vale1 vale3) | (inj₂ vale2)

progress (tcar tc₁) with progress tc₁
progress (tcar tc₁) | inj₁ (e′ , stepee′)
  = inj₁ (stepE (Ecar hole) stepee′)
progress (tcar ()) | inj₂ (natval n)
progress (tcar tc₁) | inj₂ nilval
  = inj₁ (_ , Scarnil (Dhole _))
progress (tcar tc₁) | inj₂ (consval hd tl vale1 vale2)
  = inj₁ (_ , (Scar vale1 vale2 (Dhole _) (Dhole _)))

progress (tcdr tc₁) with progress tc₁
progress (tcdr tc₁) | inj₁ (e′ , stepee′)
  = inj₁ (stepE (Ecdr hole) stepee′)
progress (tcdr ()) | inj₂ (natval n)
progress (tcdr tc₁) | inj₂ nilval
  = inj₁ (_ , Scdrnil (Dhole _))
progress (tcdr tc₁) | inj₂ (consval hd tl vale1 vale2)
  = inj₁ (_ , (Scdr vale1 vale2 (Dhole _) (Dhole _)))

progress (tx ())

progress (tbind tc₁ tc₂) with progress tc₁
progress (tbind tc₁ tc₂) | inj₁ (e′ , stepee′)
  = inj₁ (stepE (Ebind _ hole _) stepee′)
progress (tbind tc₁ tc₂) | inj₂ vale1
  = inj₁ (_ , Sbind vale1 (Dhole _) (Dhole _))

module LexicographicLE {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
                       (RelA : Rel A ℓ₁)
                       (RelB : Rel B ℓ₂) where

  open import Level
  open import Relation.Binary
  open import Induction.WellFounded
  open import Data.Product
  open import Function
  open import Induction
  open import Relation.Unary

  data _<_ : Rel (Σ A \ _ → B) (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : RelA x₁ x₂) → (x₁ , y₁) < (x₂ , y₂)
    right : ∀ {x₁ y₁ x₂ y₂} (y₁<y₂ : RelB y₁ y₂) → (x₁ ≡ x₂ ⊎ RelA x₁ x₂) →
            (x₁  , y₁) < (x₂  , y₂)

  mutual

    accessibleLE : ∀ {x y} →
                    Acc RelA x → Well-founded RelB →
                    Acc _<_ (x , y)
    accessibleLE accA wfB = acc (accessibleLE′ accA (wfB _) wfB)

    accessibleLE′ :
      ∀ {x y} →
      Acc RelA x → Acc RelB y →  Well-founded RelB →
      WfRec _<_ (Acc _<_) (x , y)
    accessibleLE′ (acc rsA) _    wfB ._ (left  x′<x) = accessibleLE (rsA _ x′<x) wfB
    accessibleLE′ accA (acc rsB) wfB .(_ , _) (right y′<y (inj₁ refl)) =
      acc (accessibleLE′ accA (rsB _ y′<y) wfB)
    accessibleLE′ (acc rsA) (acc rsB) wfB .(_ , _) (right y′<y (inj₂ x′<x)) =
      acc (accessibleLE′ (rsA _ x′<x) (rsB _ y′<y) wfB)

  well-founded : Well-founded RelA → Well-founded RelB →
                 Well-founded _<_
  well-founded wfA wfB p = accessibleLE (wfA (proj₁ p)) wfB

module _ where
  open LexicographicLE _<′_ _<′_ public
    renaming (_<_ to _<<′_;
              well-founded to <<′-well-founded;
              left to <<′-left;
              right to <<′-right)

module _ {ℓ} where
  open Induction.WellFounded.All
       (<<′-well-founded Induction.Nat.<′-well-founded Induction.Nat.<′-well-founded) ℓ public
    renaming (wfRec-builder to <<′-rec-builder;
              wfRec to <<′-rec)

≤-trans : ∀ {a b c} -> a ≤ b -> b ≤ c -> a ≤ c
≤-trans z≤n b≤c = z≤n
≤-trans (s≤s a≤b) (s≤s b≤c) = s≤s (≤-trans a≤b b≤c)

data steps : letzl -> Config -> ℕ -> Set where
  done : ∀ {e} -> steps e (eC e) 0
  dead : ∀ {e} -> step e WRONG -> steps e WRONG 1
  more : ∀ {e e′ C k} ->
    (stepee′ : step e (eC e′)) ->
    (stepse′n : steps e′ C k) ->
    steps e C (1 + k)

stepstc : ∀ {e τ k e′} ->
  tc [] e τ ->
  steps e (eC e′) k ->
  tc [] e′ τ
stepstc tce done = tce
stepstc tce (more stepee′ steps₁) =  stepstc (preservation tce stepee′) steps₁

natstepsnat : ∀ {e v k} -> (valv : val v) ->
  steps e (eC v) k ->
  tc [] e NatT ->
  ∃ (\ n -> steps e (eC (nat n)) k)
natstepsnat (natval n) stepse tce = n , stepse
natstepsnat nilval stepse tce
  with stepstc tce stepse
... | ()
natstepsnat (consval hd tl valv valv₁) stepse tce
  with stepstc tce stepse
... | ()

liststeplist : ∀ {e v k} -> (valv : val v) ->
  steps e (eC v) k ->
  tc [] e ListT ->
  steps e (eC nil) k  ⊎
  ∃ (\ { (hd , tl) -> steps e (eC (cons hd tl)) k × val hd × val tl})
liststeplist (natval n) stepse tce
  with stepstc tce stepse
... | ()
liststeplist nilval stepse tce = inj₁ stepse
liststeplist (consval hd tl valhd valtl) stepse tce
  = inj₂ ((hd , tl) , (stepse , valhd , valtl))


stepsEerr : ∀ {e k} ->
  ∀ E ->
  steps e WRONG k ->
  steps (plug E e) WRONG k
stepsEerr E (dead stepeWRONG) = dead (stepEerr E stepeWRONG)
stepsEerr E (more stepee′ stepse) = more (stepEnoerr E stepee′) (stepsEerr E stepse)

stepsEeC : ∀ {e e′ k} ->
 ∀ E ->
 steps e (eC e′) k ->
 steps (plug E e) (eC (plug E e′)) k
stepsEeC E done = done
stepsEeC E (more stepee′ stepse) = more (stepEnoerr E stepee′) (stepsEeC E stepse)

steps++ : ∀ {e₁ e₂ k₁ k₂ C} ->
 steps e₁ (eC e₂) k₁ ->
 steps e₂ C k₂ ->
 steps e₁ C (k₁ + k₂)
steps++ done stepse₂ = stepse₂
steps++ (more stepee′ stepse₁) stepse₂ = more stepee′ (steps++ stepse₁ stepse₂)

terminates : ∀ {e τ} ->
  tc [] e τ ->
  ∃ ( \ { (k′ , C) -> finishedConfig C × steps e C k′ × k′ ≤ ∥ e ∥ })
terminates = thm where

 size : letzl -> ℕ
 size (nat n) = 0
 size nil = 0
 size (cons e₁ e₂) = suc (size e₁ + size e₂)
 size (add e₁ e₂) = suc (size e₁ + size e₂)
 size (car e) = suc (size e)
 size (cdr e) = suc (size e)
 size (var n) = 0
 size (bind n e₁ e₂) = suc (size e₁ + size e₂)

 sum-boundsl : ∀ {a b c} -> a + b ≡ c ->  a ≡ c ⊎ a <′ c
 sum-boundsl {zero} {b} {zero} a+b≡s = inj₁ refl
 sum-boundsl {zero} {b} {suc c} a+b≡s = inj₂ (s≤′s z≤′n)
 sum-boundsl {suc a} {b} {zero} ()
 sum-boundsl {suc a} {b} {suc c} a+b≡s
   with sum-boundsl {a} {b} {c} (suc-inj a+b≡s) where
     suc-inj : ∀ {a b} -> suc a ≡ suc b -> a ≡ b
     suc-inj refl = refl
 sum-boundsl {suc a} {b} {suc c} a+b≡s | inj₁ x = inj₁ (cong suc x)
 sum-boundsl {suc a} {b} {suc c} a+b≡s | inj₂ y = inj₂ (s≤′s y)

 sum-boundsr : ∀ {a b c} -> a + b ≡ c -> b ≡ c ⊎ b <′ c
 sum-boundsr{a}{b} a+b≡c rewrite (+-comm a b) = sum-boundsl a+b≡c

 weaken≤ : ∀ {a b} -> suc a ≤ b -> a ≤ b
 weaken≤ (s≤s suc[a]≤b) = ≤-step suc[a]≤b

 sum-boundsl′ :  ∀ {a b c} -> a + b ≡ c ->  a ≤ c
 sum-boundsl′ {a}{b}{c} a+b≡c
   with sum-boundsl {a}{b}{c} a+b≡c
 ... | inj₁ a≡c rewrite a≡c = ≤′⇒≤ ≤′-refl
 ... | inj₂ a<′c = ≤′⇒≤ (≤⇒≤′ (weaken≤ (≤′⇒≤ a<′c)))

 sum-strict-boundsl : ∀ {a b c} -> suc (a + b) ≡ c -> a <′ c
 sum-strict-boundsl {zero} {b} {zero} ()
 sum-strict-boundsl {zero} {b} {suc c} suca+b≡c = s≤′s z≤′n
 sum-strict-boundsl {suc a} {b} {zero} ()
 sum-strict-boundsl {suc a} {b} {suc c} refl
   with sum-strict-boundsl {a} {b} {c} refl
 ... | sucsuca≤′sucsuc[a+b] = s≤′s sucsuca≤′sucsuc[a+b]

 sum-strict-boundsr : ∀ {a b c} -> suc (a + b) ≡ c -> b <′ c
 sum-strict-boundsr{a}{b}{c} eq rewrite (+-comm a b)
   = sum-strict-boundsl{b}{a}{c} eq

 le-fact : ∀ {a b} -> suc a ≡ b -> a <′ b
 le-fact x rewrite x = ≤′-refl

 ≤+r : ∀ {c a b} -> a ≤ b -> c + a ≤ c + b
 ≤+r {zero} {a} {b} a≤b = a≤b
 ≤+r {suc c} {a} {b} a≤b = s≤s (≤+r {c} a≤b)

 ≤+l : ∀ {c a b} -> a ≤ b -> a + c ≤ b + c
 ≤+l {c}{a}{b} a≤b rewrite +-comm a c | +-comm b c = ≤+r{c} a≤b

 ≤+≤ : ∀ {a b c d} -> a ≤ b -> c ≤ d -> a + c ≤ b + d
 ≤+≤{a}{b}{c}{d} a≤b c≤d = ≤-trans (≤+l a≤b) (≤+r {b} c≤d)

 ≡->≤ : ∀ {a b} -> a ≡ b -> a ≤ b
 ≡->≤ a≡b rewrite a≡b = ≤′⇒≤ ≤′-refl

 tstep-result : ℕ × ℕ -> Set
 tstep-result (the-work , the-size) =
   ∀ {e τ} ->
    tc [] e τ ->
    ∥ e ∥ ≡ the-work ->
    size e ≡ the-size ->
    ∃ ( \ { (k′ , C) -> finishedConfig C × steps e C k′ × k′ ≤ the-work })

 tstep : ∀ sd ->
        (∀ (sd′ : ℕ × ℕ) -> sd′ <<′ sd -> tstep-result sd′) ->
        tstep-result sd

 tstep (s , d) R tnat ∥e∥≡s sizee≡d = (0 , _) , finVal (natval _) , done , z≤n

 tstep (s , d) R tnil ∥e∥≡s sizee≡d = (0 , _) , finVal nilval , done , z≤n

 tstep (s , d) R {cons e₁ e₂} (tcons tc₁ tc₂) ∥e∥≡s sizee≡d
  with R _ (<<′-right (sum-strict-boundsl sizee≡d) (sum-boundsl ∥e∥≡s))
           tc₁ refl refl
      | R _ (<<′-right (sum-strict-boundsr{size e₁} sizee≡d)
            (sum-boundsr{∥ e₁ ∥} ∥e∥≡s))
          tc₂ refl refl
 ... | (k₁ , WRONG) , finWRONG , stepse₁k₁ , k₁≤k₁′
     | (k₂ , C₂) , _ , stepse₂k₂ , k₂≤k₂′
     = (k₁ , WRONG) , finWRONG ,
       stepsEerr (Econsl hole e₂) stepse₁k₁ ,
       ≤-trans k₁≤k₁′ (sum-boundsl′ ∥e∥≡s)
 ... | (k₁ , eC v) , finVal valv , stepse₁k₁ , k₁≤k₁′
     | (k₂ , WRONG) , finWRONG , stepse₂k₂ , k₂≤k₂′
     = (k₁ + k₂ , WRONG) , finWRONG ,
       steps++ (stepsEeC (Econsl hole e₂) stepse₁k₁)
               (stepsEerr (Econsr v valv hole) stepse₂k₂) ,
       ≤-trans (≤+≤ k₁≤k₁′ k₂≤k₂′) (≡->≤ ∥e∥≡s)
 ... | (k₁ , eC v₁) , finVal valv₁ , stepse₁k₁ , k₁≤k₁′
     | (k₂ , eC v₂) , finVal valv₂ , stepse₂k₂ , k₂≤k₂′
     = (k₁ + k₂ , (eC (cons v₁ v₂))) ,
       finVal (consval v₁ v₂ valv₁ valv₂) ,
       steps++ (stepsEeC (Econsl hole e₂) stepse₁k₁)
               (stepsEeC (Econsr v₁ valv₁ hole) stepse₂k₂) ,
       ≤-trans (≤+≤ k₁≤k₁′ k₂≤k₂′) (≡->≤ ∥e∥≡s)

 tstep (s , d) R {add e₁ e₂} (tadd tc₁ tc₂) ∥e∥≡s sizee≡d
   with R _ (<<′-right (sum-strict-boundsl sizee≡d)
                       (inj₂ (sum-strict-boundsl ∥e∥≡s)))
          tc₁ refl refl
      | R _ (<<′-right (sum-strict-boundsr{size e₁} sizee≡d)
            (inj₂ (sum-strict-boundsr{∥ e₁ ∥} ∥e∥≡s)))
          tc₂ refl refl
 ... | (k₁ , WRONG) , finWRONG , stepse₁k₁ , k₁≤k₁′
     | (k₂ , C₂) , _ , stepse₂k₂ , k₂≤k₂′
     = (k₁ , WRONG) , finWRONG ,
       stepsEerr (E+l hole e₂) stepse₁k₁ ,
       ≤-trans k₁≤k₁′ (weaken≤ (≤′⇒≤ (sum-strict-boundsl{∥ e₁ ∥} ∥e∥≡s)))
 ... | (k₁ , eC v) , finVal valv , stepse₁k₁ , k₁≤k₁′
     | (k₂ , WRONG) , finWRONG , stepse₂k₂ , k₂≤k₂′
     = (k₁ + k₂ , WRONG) , finWRONG ,
       steps++ (stepsEeC (E+l hole e₂) stepse₁k₁)
               (stepsEerr (E+r v valv hole) stepse₂k₂) ,
        ≤-trans (≤+≤ k₁≤k₁′ k₂≤k₂′) (weaken≤ (≡->≤ ∥e∥≡s))
 ... | (k₁ , eC v₁) , finVal valv₁ , stepse₁k₁ , k₁≤k₁′
     | (k₂ , eC v₂) , finVal valv₂ , stepse₂k₂ , k₂≤k₂′
     with natstepsnat valv₁ stepse₁k₁ tc₁ | natstepsnat valv₂ stepse₂k₂ tc₂
 ... | n₁ , stepse₁n₁ | n₂ , stepse₂n₂
     = (k₁ + k₂ + 1 , eC (nat (n₁ + n₂))) , finVal (natval (n₁ + n₂)) ,
        steps++ (steps++ (stepsEeC (E+l hole e₂) stepse₁n₁)
                         (stepsEeC (E+r (nat n₁) (natval n₁) hole) stepse₂n₂))
                (more (Sadd (Dhole (add (nat n₁) (nat n₂))) (Dhole (nat (n₁ + n₂))))
                      done) ,
       ≤-trans (≡->≤ (+-comm (k₁ + k₂) 1))
               (≤-trans (s≤s (≤+≤ k₁≤k₁′ k₂≤k₂′)) (≡->≤ ∥e∥≡s))

 tstep (s , d) R {car e} (tcar tce) ∥e∥≡s sizee≡d
    with R _ (<<′-right (le-fact sizee≡d) (inj₂ (le-fact ∥e∥≡s))) tce refl refl
 ... | (k , WRONG) , finWRONG , stepsek , k≤k′
   = (k , WRONG) , finWRONG ,
     stepsEerr (Ecar hole) stepsek ,
     ≤-trans k≤k′ (≤-trans (n≤1+n ∥ e ∥) (≡->≤ ∥e∥≡s))
 ... | (k , eC v) , finVal valv , stepsek , k≤k′
   with liststeplist valv stepsek tce
 ... | inj₁ stepsenil
   = (k + 1 , WRONG) , finWRONG ,
      steps++ (stepsEeC (Ecar hole) stepsenil) (dead (Scarnil (Dhole _))) ,
      ≤-trans (≡->≤ (+-comm k 1)) (≤-trans (s≤s k≤k′) (≡->≤ ∥e∥≡s))
 ... | inj₂ ((hd , tl) , stepsecons , valhd , valtl)
   = ((k + 1) , eC hd) , finVal valhd ,
     steps++ (stepsEeC (Ecar hole) stepsecons)
             (more (Scar valhd valtl (Dhole _) (Dhole _)) done) ,
     ≤-trans (≡->≤ (+-comm k 1)) (≤-trans (s≤s k≤k′) (≡->≤ ∥e∥≡s))

 tstep (s , d) R {cdr e} (tcdr tce) ∥e∥≡s sizee≡d
    with R _ (<<′-right (le-fact sizee≡d) (inj₂ (le-fact ∥e∥≡s))) tce refl refl
 ... | (k , WRONG) , finWRONG , stepsek , k≤k′
   = (k , WRONG) , finWRONG ,
     stepsEerr (Ecdr hole) stepsek ,
     ≤-trans k≤k′ (≤-trans (n≤1+n ∥ e ∥) (≡->≤ ∥e∥≡s))
 ... | (k , eC v) , finVal valv , stepsek , k≤k′
   with liststeplist valv stepsek tce
 ... | inj₁ stepsenil
   = (k + 1 , WRONG) , finWRONG ,
      steps++ (stepsEeC (Ecdr hole) stepsenil) (dead (Scdrnil (Dhole _))) ,
      ≤-trans (≡->≤ (+-comm k 1)) (≤-trans (s≤s k≤k′) (≡->≤ ∥e∥≡s))
 ... | inj₂ ((hd , tl) , stepsecons , valhd , valtl)
   = ((k + 1) , eC tl) , finVal valtl ,
     steps++ (stepsEeC (Ecdr hole) stepsecons)
             (more (Scdr valhd valtl (Dhole _) (Dhole _)) done) ,
     ≤-trans (≡->≤ (+-comm k 1)) (≤-trans (s≤s k≤k′) (≡->≤ ∥e∥≡s))

 tstep (s , d) R (tx ()) ∥e∥≡s sizee≡d

 tstep (s , d) R {bind x e₁ e₂} (tbind tc₁ tc₂) ∥e∥≡s sizee≡d
   with R _ (<<′-right (sum-strict-boundsl sizee≡d)
                       (inj₂ (sum-strict-boundsl ∥e∥≡s)))
          tc₁ refl refl
 ... | (k₁ , WRONG) , finWRONG , stepse₁WRONG , k₁≤k₁′
   = (k₁ , WRONG) , finWRONG ,
     stepsEerr (Ebind x hole e₂) stepse₁WRONG ,
     ≤-trans k₁≤k₁′ (weaken≤ (≤′⇒≤ (sum-strict-boundsl{∥ e₁ ∥} ∥e∥≡s)))
 ... | (k₁ , eC v) , finVal valv , stepse₁k₁ , k₁≤∥e₁∥
   with R (∥ subst x e₂ valv ∥ , size (subst x e₂ valv))
          (<<′-left (sum-strict-boundsr{∥ e₁ ∥}
                       (trans (cong (λ { x₁ → suc (∥ e₁ ∥ + x₁) })
                                    (subst-preserves-size x e₂ valv))
                              ∥e∥≡s)))
          (substitution valv tc₂ (stepstc tc₁ stepse₁k₁)) refl refl
 ... | (k₂ , WRONG) , finWRONG , stepssubst , k₂≤∥substxe₂∥
  = (k₁ + suc k₂ , WRONG) , finWRONG ,
    steps++ (stepsEeC (Ebind x hole e₂) stepse₁k₁)
            (more (Sbind valv (Dhole _) (Dhole _)) stepssubst) ,
    ≤-trans (≡->≤ (+-suc k₁ k₂))
            (≤-trans (s≤s (≤+≤ k₁≤∥e₁∥
                               (≤-trans k₂≤∥substxe₂∥
                                        (≡->≤ (subst-preserves-size x e₂ valv)))))
                     (≡->≤ ∥e∥≡s))
 ... | (k₂ , eC v′) , finVal valv′ , stepssubst , k₂≤∥substxe₂∥
  = (k₁ + suc k₂ , (eC v′)) , finVal valv′ ,
    steps++ (stepsEeC (Ebind x hole e₂) stepse₁k₁)
            (more (Sbind valv (Dhole _) (Dhole _))
                  stepssubst) ,
    ≤-trans (≡->≤ (+-suc k₁ k₂))
            (≤-trans (s≤s (≤+≤ k₁≤∥e₁∥
                               (≤-trans k₂≤∥substxe₂∥
                                        (≡->≤ (subst-preserves-size x e₂ valv)))))
                     (≡->≤ ∥e∥≡s))

 thm :  ∀ {e τ} ->
   tc [] e τ ->
   ∃ ( \ { (k′ , C) -> finishedConfig C × steps e C k′ × k′ ≤ ∥ e ∥ })
 thm tc = (<<′-rec _ tstep) _ tc refl refl
