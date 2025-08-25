module _ where

open import nat
open import eq
open import sum
open import product

data Bt : Set where
  leaf : Bt
  node : (n : ℕ) -> (l : Bt) -> (r : Bt) -> Bt

data Perfect : Bt -> ℕ -> Set where
 leaf : Perfect leaf 0
 node : ∀ { n bt1 bt2 } val ->
   Perfect bt1 n ->
   Perfect bt2 n ->
   Perfect (node val bt1 bt2) (suc n)

perfect-leaf-i : ∀ { n } ->
  Perfect leaf n ->
  n ≡ 0
perfect-leaf-i leaf = refl

perfect-node-i : ∀ { n val bt1 bt2 } ->
  Perfect (node val bt1 bt2) n ->
  Σ[ n' ∈ ℕ ]
  n ≡ suc n' ×
  Perfect bt1 n' ×
  Perfect bt2 n'
perfect-node-i (node _ perf1 perf2)
 = _ , refl , perf1 , perf2

perfect-zero-i : ∀ { bt } ->
  Perfect bt 0 ->
  bt ≡ leaf
perfect-zero-i leaf = refl

perfect-suc-i : ∀ { bt n } ->
  Perfect bt (suc n) ->
  Σ[ val ∈ ℕ ]
  Σ[ bt1 ∈ Bt ]
  Σ[ bt2 ∈ Bt ]
  bt ≡ node val bt1 bt2 ×
  Perfect bt1 n ×
  Perfect bt2 n
perfect-suc-i (node val perf1 perf2)
 = val , _ , _ , refl , perf1 , perf2

data Complete : Bt -> ℕ -> Set where
 leaf : Complete leaf 0
 right : ∀ { n bt1 bt2 } val ->
  Perfect bt1 n ->
  Complete bt2 n ->
  Complete (node val bt1 bt2) (suc n)
 left : ∀ { n bt1 bt2 } val ->
  Complete bt1 (suc n) ->
  Perfect bt2 n ->
  Complete (node val bt1 bt2) (suc (suc n))

complete-leaf-i : ∀ { n } ->
  Complete leaf n ->
  n ≡ zero
complete-leaf-i leaf = refl

complete-node-i : ∀ { val bt1 bt2 n } ->
  Complete (node val bt1 bt2) n ->
  (Σ[ n' ∈ ℕ ]
   n ≡ suc n' ×
   Perfect bt1 n' ×
   Complete bt2 n') ∨
  (Σ[ n' ∈ ℕ ]
   n ≡ suc (suc n') ×
   Complete bt1 (suc n') ×
   Perfect bt2 n')
complete-node-i (right _ x compl)
 = inj₁ (_ , refl , x , compl)
complete-node-i (left _ compl x)
 = inj₂ (_ , refl , compl , x)

complete-zero-i : ∀ { bt } ->
  Complete bt zero ->
  bt ≡ leaf
complete-zero-i leaf = refl

complete-suc-i : ∀ { bt n } ->
  Complete bt (suc n) ->
  Σ[ val ∈ ℕ ]
  Σ[ bt1 ∈ Bt ]
  Σ[ bt2 ∈ Bt ]
  bt ≡ node val bt1 bt2 ×
  (Perfect bt1 n ×
   Complete bt2 n ∨
   Σ[ n' ∈ ℕ ]
   n ≡ suc n' ×
   Complete bt1 n ×
   Perfect bt2 n')
complete-suc-i (right val x compl)
 = _ , _ , _ , refl , inj₁ (x , compl)
complete-suc-i (left val compl x)
 = _ , _ , _ , refl , inj₂ (_ , refl , compl , x)


perfect-is-complete : ∀ bt n ->
  Perfect bt n ->
  Complete bt n
perfect-is-complete bt n leaf = leaf
perfect-is-complete bt n (node val perfl perfr)
 = right val perfl (perfect-is-complete _ _ perfr)

data C : Set where
 hole : C
 left : (z : ℕ) -> (bt : Bt) -> (c : C) -> C
 right : (z : ℕ) -> (bt : Bt) -> (c : C) -> C

plug : C -> Bt -> Bt
plug hole bt = bt
plug (left x l C) bt = node x l (plug C bt)
plug (right x r C) bt = node x (plug C bt) r

++c : C -> C -> C
++c hole c2 = c2
++c (left z bt c1) c2 = left z bt (++c c1 c2)
++c (right z bt c1) c2 = right z bt (++c c1 c2)

data Step : Bt -> Bt -> Set where
 two : ∀ c z1 z2 z3 ->
  Step (plug c (node z1 (node z2 leaf leaf) (node z3 leaf leaf)))
       (plug c (node z1 (node (z2 + z3) leaf leaf) leaf))
 one : ∀ c z1 z2 ->
  Step (plug c (node z1 (node z2 leaf leaf) leaf))
       (plug c (node (z1 + z2) leaf leaf))

plug++ : ∀ c1 c2 bt ->
 plug c1 (plug c2 bt) ≡ plug (++c c1 c2) bt
plug++ hole c2 bt = refl
plug++ (left z bt₁ c1) c2 bt rewrite plug++ c1 c2 bt = refl
plug++ (right z bt₁ c1) c2 bt rewrite plug++ c1 c2 bt = refl

step-c : ∀ c bt bt' ->
  Step bt bt' ->
  Step (plug c bt) (plug c bt')
step-c c1 bt bt1' (two c2 z1 z2 z3) rewrite
   plug++ c1 c2 (node z1 (node z2 leaf leaf) (node z3 leaf leaf))
 | plug++ c1 c2 (node z1 (node (z2 + z3) leaf leaf) leaf)
 = two (++c c1 c2) z1 z2 z3
step-c c1 bt bt1' (one c2 z1 z2) rewrite
   plug++ c1 c2 (node z1 (node z2 leaf leaf) leaf)
 | plug++ c1 c2 (node (z1 + z2) leaf leaf)
 = one (++c c1 c2) z1 z2

lem : ∀ bt n ->
  Complete bt n ->
  bt ≡ leaf ∨
  (Σ[ z ∈ ℕ ]
   bt ≡ node z leaf leaf) ∨
  (Σ[ bt' ∈ Bt ]
   Complete bt' n ×
   Step bt bt') ∨
  (Σ[ bt' ∈ Bt ]
   Σ[ n' ∈ ℕ ]
   n ≡ suc n' ×
   Perfect bt' n' ×
   Step bt bt')
lem leaf               n complete = inj₁ refl
lem (node val bt1 bt2) n complete with complete-node-i complete
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) with lem bt2 n' comp-bt2
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₁ refl with complete-leaf-i comp-bt2
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₁ refl | refl with perfect-zero-i perf-bt1
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₁ refl | refl | refl = inj₂ (inj₁ (val , refl))
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₂ (inj₁ (z , refl)) with complete-node-i comp-bt2
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₂ (inj₁ (z , refl)) | inj₁ (n'' , refl , perf-l , comp-l) with complete-leaf-i comp-l
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₂ (inj₁ (z , refl)) | inj₁ (n'' , refl , perf-l , comp-l) | refl with perfect-suc-i perf-bt1
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₂ (inj₁ (z , refl)) | inj₁ (n'' , refl , perf-l , comp-l) | refl | _ , bt3 , bt4 , refl , perf-bt3 , perf-bt4 with perfect-zero-i perf-bt3 | perfect-zero-i perf-bt4
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₂ (inj₁ (z , refl)) | inj₁ (n'' , refl , perf-l , comp-l) | refl | _ , bt3 , bt4 , refl , perf-bt3 , perf-bt4 | refl | refl = inj₂ (inj₂ (inj₁ (plug hole (node val (node _ leaf leaf) leaf) , left val (right _ perf-bt3 comp-l) perf-bt3 , two hole val _ _)))
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₂ (inj₁ (z , refl)) | inj₂ (n'' , refl , comp-l , perf-l) with complete-leaf-i comp-l
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₂ (inj₁ (z , refl)) | inj₂ (n'' , refl , comp-l , perf-l) | ()
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₂ (inj₂ (inj₁ (bt2' , comp-bt2' , step))) = inj₂ (inj₂ (inj₁ (node val bt1 bt2' , right val perf-bt1 comp-bt2' , step-c (left val bt1 hole) bt2 bt2' step)))
lem (node val bt1 bt2) n complete | inj₁ (n' , refl , perf-bt1 , comp-bt2) | inj₂ (inj₂ (inj₂ (bt2' , n'' , refl , perf-bt2' , step))) = inj₂ (inj₂ (inj₁ (plug (left val bt1 hole) bt2' , left val (perfect-is-complete _ _  perf-bt1) perf-bt2' , step-c (left val bt1 hole) bt2 bt2' step)))
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) with lem bt1 (suc n') comp-bt1
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) | inj₁ refl with complete-leaf-i comp-bt1
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) | inj₁ refl | ()
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) | inj₂ (inj₁ (z , refl)) with complete-node-i comp-bt1
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) | inj₂ (inj₁ (z , refl)) | inj₁ (n'' , refl , perf-l , comp-l) with complete-leaf-i comp-l
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) | inj₂ (inj₁ (z , refl)) | inj₁ (n'' , refl , perf-l , comp-l) | refl with perfect-zero-i perf-bt2
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) | inj₂ (inj₁ (z , refl)) | inj₁ (n'' , refl , perf-l , comp-l) | refl | refl = inj₂ (inj₂ (inj₂ (node (val + z) leaf leaf , 1 , refl , node (val + z) perf-bt2 perf-bt2 , one hole val z)))
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) | inj₂ (inj₁ (z , refl)) | inj₂ (n'' , refl , comp-l , perf-l) with complete-leaf-i comp-l
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) | inj₂ (inj₁ (z , refl)) | inj₂ (n'' , refl , comp-l , perf-l) | ()
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) | inj₂ (inj₂ (inj₁ (bt1' , comp-bt1' , step))) = inj₂ (inj₂ (inj₁ (node val bt1' bt2 , left val comp-bt1' perf-bt2 , step-c (right val bt2 hole) bt1 bt1' step)))
lem (node val bt1 bt2) n complete | inj₂ (n' , refl , comp-bt1 , perf-bt2) | inj₂ (inj₂ (inj₂ (bt1' , n'' , refl , perf-bt1' , step))) = inj₂ (inj₂ (inj₂ (node val bt1' bt2 , suc n' , refl , node val perf-bt1' perf-bt2 , step-c (right val bt2 hole) _ _ step)))
