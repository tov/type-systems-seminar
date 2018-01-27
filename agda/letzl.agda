module _ where

open import Data.Nat
  using (ℕ ; _≟_ ; suc ; _+_)
open import Relation.Nullary
  using (yes ; no ; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym)
open import Data.List
  using (List ; _∷_ ; [])
open import Data.Product
  using (_,_ ; _,′_ ; _×_ ; proj₁ ; proj₂ ; ∃)
open import Data.Empty
  using (⊥ ; ⊥-elim)

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

data step : letzl -> Config -> Set where
  s_add : ∀ {n₁ n₂ e₁ e₂ E} ->
     decomp e₁ E (add (nat n₁) (nat n₂)) ->
     decomp e₂ E (nat (n₁ + n₂)) ->
     step e₁ (eC e₂)
  s_car : ∀ {v₁ v₂ e₁ e₂ E} -> val v₁ -> val v₂ ->
    decomp e₁ E (car (cons v₁ v₂)) -> 
    decomp e₂ E v₁ -> 
    step e₁ (eC e₂)
  s_cdr : ∀ {v₁ v₂ e₁ e₂ E} -> val v₁ -> val v₂ ->
    decomp e₁ E (car (cons v₁ v₂)) -> 
    decomp e₂ E v₂ -> 
    step e₁ (eC e₂)
  s_bind : ∀ {x v e e₁ e₂ E} -> (valv : val v) ->
    decomp e₁ E (bind x v e) -> 
    decomp e₂ E (subst x e valv) -> 
    step e₁ (eC e₂)
  s_carnil : ∀ {e₁ E} ->
    decomp e₁ E (car nil) ->
    step e₁ WRONG
  s_cdrnil : ∀ {e₁ E} ->
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
