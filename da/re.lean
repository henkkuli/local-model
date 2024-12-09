import Mathlib

section Sorting
  variable {α : Type*} [instPreorder : Preorder α]

  abbrev List.IsSorted (l : List α) : Prop := l.Pairwise instPreorder.le

  lemma nil_is_sorted : ([] : List α).IsSorted := by simp
  lemma singleton_is_sorted (a : α) : [a].IsSorted := by simp

  variable [DecidableRel instPreorder.le]
  def merge : List α → List α → List α
  -- | [], [] => []
  | [], a' => a'
  | a, [] => a
  | a :: rest, a' :: rest' =>
    if a <= a' then
      a :: merge rest (a' :: rest')
    else
      a' :: merge (a :: rest) rest'

  theorem is_sorted_is_sorted_merge_is_sorted : ∀ l₁ l₂ : List α, l₁.IsSorted → l₂.IsSorted → (merge l₁ l₂).IsSorted := by
    intro l₁ l₂ h₁ h₂
    induction l₁ with
    | nil =>
      rw [merge]
      assumption
      -- · assumption
      -- · intro h
      --   sorry
    | cons a₁ t₁ ih₁ =>
      induction l₂ with
      | nil =>
        rw [merge]
        assumption
        simp
      | cons a₂ t₂ ih₂ =>
        rw [merge]
        by_cases ha : a₁ ≤ a₂
        simp_rw [ha]
        reduce


        sorry

end Sorting

theorem horseColors (V : Type) (s : Finset V) : ∀ a ∈ s, ∀ b ∈ s, a = b := by
  classical
  apply s.strongInduction
  intro s' h a ha b hb
  let s'a := s'.erase a
  let s'b := s'.erase b
  -- have h' := h s'a (Finset.erase_ssubset ha) b sorry
  sorry

abbrev MultisetOfCard (V : Type*) (c : ℕ) := { s : Multiset V // Multiset.card s = c}

def MultisetOfCard.cons {V : Type*} {c : ℕ} : V → MultisetOfCard V c → MultisetOfCard V (c+1) :=
  fun a m => ⟨a ::ₘ m, by simp⟩

infix:67 " ::ₘₘ " => MultisetOfCard.cons

instance MultisetOfCard.instMembership V d : Membership V (MultisetOfCard V d) :=
  ⟨fun a s => a ∈ s.val⟩

instance MultisetOfCard.decidableMem (a : V) (s : MultisetOfCard V d) [DecidableEq V] : Decidable (a ∈ s) := (inferInstance : Decidable (a ∈ s.val))

def MultisetOfCard.fintype [fintypeV : Fintype V] [DecidableEq V] : (d : ℕ) → Fintype (MultisetOfCard V d)
| 0 => {
  elems := { ⟨∅, by simp⟩ }
  complete := by
    intro x

    rw [MultisetOfCard] at x
    obtain ⟨s, h⟩ := x
    exact s.recOn (by
      simp
      -- apply Subtype.ext
      ext
      have : ↑x = s := by
        simp_all only [Multiset.card_eq_zero, Sym.val_eq_coe]
        subst h
        obtain ⟨val, property⟩ := x
        simp_all only [Sym.coe_mk]
        simp_all only [Multiset.card_eq_zero]
      rw [this]
      simp_all
    ) (by simp) (by simp)
}
| k + 1 =>
  let combine : V × (MultisetOfCard V k) → MultisetOfCard V (k+1) := fun ⟨a, b⟩ =>
    let m := a ::ₘ b.val
    ⟨m, by simp only [Sym.val_eq_coe, Multiset.card_cons, Sym.card_coe, m]⟩
  {
    elems := (fintypeV.elems ×ˢ (MultisetOfCard.fintype (V := V) k).elems).image $ combine
    complete := by
      intro x
      obtain ⟨s₁, h⟩ := x
      let s := s₁.toList
      have h : s.length = k + 1 := by simp only [Multiset.length_toList, s, h]
      match hₛ : s with
      | .nil =>
        absurd Nat.succ_ne_zero k
        rw [←List.length_nil]
        exact h.symm
      | a :: prev =>
        have : ↑(a :: prev) = s₁ := by
          have : s = s₁.toList := rfl
          rw [←hₛ, this]
          exact Multiset.coe_toList _

        simp
        let prev : Multiset V := prev
        have : Multiset.card prev = k := by simp_all only [List.length_cons, add_left_inj, Multiset.coe_card, prev]
        use a, ↑prev, this
        constructor
        · constructor
          · exact Fintype.complete a
          · exact (MultisetOfCard.fintype k).complete _
        · simp_all only [combine, List.length_cons, Multiset.coe_card, Multiset.cons_coe, prev, s]
}

instance MultisetOfCard.instFintype V d [Fintype V] [DecidableEq V] : Fintype (MultisetOfCard V d) := MultisetOfCard.fintype d

instance MultisetOfCard.instEmptyCollection V : EmptyCollection (MultisetOfCard V 0) where
  emptyCollection := ⟨∅, by simp⟩

theorem MultisetOfCard.card_zero_eq_empty : ∀ s : MultisetOfCard V 0, s = ∅ := by
  intro s
  obtain ⟨s, h⟩ := s
  simp_rw [Multiset.card_eq_zero.mp h]
  rfl

def MultisetOfCard.map (f : V → U) (m : MultisetOfCard V c): MultisetOfCard U c :=
  let ⟨m, h⟩ := m
  ⟨m.map f, by simp only [Multiset.card_map, h]⟩

-- theorem MultisetOfCard.map_coe : ∀ (f : V → U) (m : MultisetOfCard V c), Multiset.map f ↑m = ↑(MultisetOfCard.map f m) := sorry


theorem MultisetOfCard.cons_coe : ∀ (a : V) (m : MultisetOfCard V c), a ::ₘₘ m = a ::ₘ m := by
  intro a m
  rfl

theorem MultisetOfCard.map_cons : ∀ (f : V → U) (a : V) (m : MultisetOfCard V c), (a ::ₘₘ m).map f = f a ::ₘₘ m.map f := by
  intro f a m
  simp_rw [map, cons_coe, Multiset.map_cons]
  rfl

theorem MultisetOfCard.coe_eq : ∀ (a b : MultisetOfCard V c), (↑a : Multiset V) = ↑b → a = b := by simp

theorem MultisetOfCard.induction {p : (c : ℕ) → MultisetOfCard V c → Prop} (empty : p 0 ∅) (cons : ∀ ⦃a : V⦄ ⦃c : ℕ⦄ {s : MultisetOfCard V c}, p c s → p (c + 1) (a ::ₘₘ s)) : ∀ s : MultisetOfCard V c, p c s := by
  rintro ⟨⟨s⟩, h⟩
  simp only [Multiset.quot_mk_to_coe'', Multiset.coe_card] at h
  induction s generalizing c with
  | nil =>
    subst h
    exact empty
  | cons a tail ih =>
    have := h ▸ List.length_cons a tail
    subst this
    exact @cons _ _ _ (@ih tail.length rfl)

theorem MultisetOfCard.induction_on {p : (c : ℕ) → MultisetOfCard V c → Prop} (s : MultisetOfCard V c) (empty : p 0 ∅) (cons : ∀ ⦃a : V⦄ ⦃c : ℕ⦄ {s : MultisetOfCard V c}, p c s → p (c + 1) (a ::ₘₘ s)) : p c s := s.induction empty cons

def Configuration (V : Type*) (d : ℕ) := Fin d → V

def Configuration.toMultiset (config : Configuration V d) : MultisetOfCard V d :=
  ⟨List.ofFn config, List.length_ofFn config⟩

def Configuration.coeMultiset : Coe (Configuration V d) (MultisetOfCard V d) := ⟨Configuration.toMultiset⟩

-- instance MultisetOfCard.configurationMembership V d : Membership (Configuration V d) (MultisetOfCard V d) :=
--   ⟨fun config s => config.toMultiset ∈ s⟩


structure BipartiteLCL (V : Type u) (a p : ℕ) where
  active : Finset (MultisetOfCard V a)
  passive : Finset (MultisetOfCard V p)

unsafe instance BipartiteLCL.instRepr [Repr V] : Repr (BipartiteLCL V a p) where
reprPrec := fun π _ =>
  let active := Std.Format.text "active: " ++ Repr.reprPrec π.active 0
  let passive := Std.Format.text "passive: " ++ Repr.reprPrec π.passive 0
  .join [active, .line, passive]

def BipartiteLCL.swap (π : BipartiteLCL V a p) : BipartiteLCL V p a where
  active := π.passive
  passive := π.active


def TrivialLCL V [Fintype V] [DecidableEq V] a p : BipartiteLCL V a p where
  active := Fintype.elems
  passive := Fintype.elems

def EmptyLCL V a p : BipartiteLCL V a p where
  active := ∅
  passive := ∅

def SinklessOrientation (d : ℕ) : BipartiteLCL Bool d 2 where
  active := { s : MultisetOfCard Bool d | true ∈ s }
  passive := { ⟨{false, true}, by simp⟩ }


structure CondensedBipartiteLCL (V : Type u) (a p : ℕ) where
  active : Finset (MultisetOfCard (Finset V) a)
  passive : Finset (MultisetOfCard (Finset V) p)

#eval! SinklessOrientation 5


variable {V : Type*} [Fintype V] [DecidableEq V]
variable {U : Type*} [Fintype U] [DecidableEq U]

def transposeMultiset : Multiset (Multiset V) → Multiset (Multiset V) :=
  let inner : Multiset V → Multiset (Multiset V) → Multiset (Multiset V) :=
    fun next prev =>
      next.bind fun a =>
        prev.bind fun b =>
          { a ::ₘ b }

  have inner_commutative : LeftCommutative (α := Multiset V) inner := by
    intro a b rest
    unfold_let inner
    beta_reduce
    conv =>
      lhs
      arg 2
      ext
      rw [Multiset.bind_assoc]
    conv =>
      rhs
      arg 2
      ext
      rw [Multiset.bind_assoc]
    rw [Multiset.bind_bind]
    simp [Multiset.cons_swap]

  Multiset.foldr inner inner_commutative { {} }

def transposeFinset : Multiset (Finset V) → Finset (Multiset V) :=
  fun m => (transposeMultiset $ m.map Finset.val).toFinset

theorem Finset.biUnion_comm [DecidableEq γ] (m : Finset α) (n : Finset β) {f : α → β → Finset γ} : (m.biUnion fun a => n.biUnion fun b => f a b) = n.biUnion fun b => m.biUnion fun a => f a b := by
  -- Thanks aesop :)
  ext1 a
  simp_all only [mem_biUnion]
  apply Iff.intro
  · intro a_1
    obtain ⟨w, h⟩ := a_1
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    apply Exists.intro
    · apply And.intro
      · exact left_1
      · apply Exists.intro
        · apply And.intro
          on_goal 2 => {exact right
          }
          · simp_all only
  · intro a_1
    obtain ⟨w, h⟩ := a_1
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    apply Exists.intro
    · apply And.intro
      · exact left_1
      · apply Exists.intro
        · apply And.intro
          on_goal 2 => {exact right
          }
          · simp_all only

def Subtype.Finset.to_Finset_Subtype.inner {p : α → Prop} (m : Finset α) (h : ∀ e ∈ m, p e) : { s : α // s ∈ m } ↪ { e : α // p e } := {
  toFun := fun ⟨e, h'⟩ => ⟨e, h e h'⟩
  inj' := by
    intro a b h
    rename_i x h_1
    simp only [Subtype.mk.injEq] at h
    rw [Subtype.mk.injEq]
    assumption
}
def Subtype.Finset.to_Finset_Subtype {p : α → Prop} : { s : Finset α // ∀ e ∈ s, p e } → Finset { e : α // p e } :=
  fun ⟨m, h⟩  =>
    m.attach.map $ Subtype.Finset.to_Finset_Subtype.inner m h

-- theorem Subtype.Finset.to_Finset_Subtype.ext

def subconfigurations.inner : Finset V → Finset (Multiset V) → Finset (Multiset V) :=
  fun next prev =>
    next.biUnion fun a =>
      prev.biUnion fun b =>
        { a ::ₘ b }


theorem subconfigurations.inner.left_commutative : LeftCommutative (α := Finset V) inner := by
  intro a b rest
  simp_rw [inner, Finset.biUnion_biUnion]
  conv =>
    enter [1, 2, a, 2, a]
    rw [Finset.biUnion]
    rw [Multiset.toFinset]
    enter [1, 1]
    simp
    enter [1, a]
    rw [Multiset.cons_swap]
  conv =>
    enter [2, 2, a, 2, a]
    rw [Finset.biUnion]
    simp
    rw [Multiset.toFinset]
    enter [1, 1]
    simp

  rw [Finset.biUnion_comm]

theorem subconfigurations.inner_card (d : ℕ) : ∀ (next : Finset V) (prev : Finset (Multiset V)), (∀ e ∈ prev, Multiset.card e = d) → ∀ e ∈ subconfigurations.inner next prev, Multiset.card e = d + 1 := by
    intro next prev h e h_e
    rw [inner] at h_e
    rw [Finset.mem_biUnion] at h_e
    obtain ⟨n, h_n, h_p⟩ := h_e
    rw [Finset.mem_biUnion] at h_p
    obtain ⟨s, h_s, h_e⟩ := h_p
    rw [Multiset.mem_singleton.mp h_e, ←h s h_s]
    exact Multiset.card_cons _ _

def subconfigurations : MultisetOfCard (Finset V) d → Finset (MultisetOfCard V d) :=
  have foldr_card (d : ℕ) (moc : MultisetOfCard (Finset V) d) : ∀ e ∈ moc.val.foldr subconfigurations.inner subconfigurations.inner.left_commutative { {} }, Multiset.card e = d := by
    induction' d with k ih
    case zero =>
      obtain ⟨m, hm⟩ := moc
      have : m = {} := by simp_all only [Multiset.card_eq_zero, Multiset.empty_eq_zero]
      simp [this]

    case succ =>
      obtain ⟨m, hm⟩ := moc
      have : m = m.toList := (Multiset.coe_toList _).symm
      dsimp
      rw [←Multiset.coe_toList m, Multiset.coe_foldr]
      match h : m.toList with
      | [] =>
        rw [this, Multiset.coe_card, h, List.length_nil] at hm
        exfalso
        exact Nat.succ_ne_zero k hm.symm
      | head :: tail =>
        rw [List.foldr_cons]
        have : tail.length = k := by
          have : m.toList.length = k + 1 := by simp [hm]
          apply (add_left_inj 1).mp
          rw [←this, h]
          symm
          exact List.length_cons _ _
        apply subconfigurations.inner_card
        rw [←Multiset.coe_foldr]
        exact ih ⟨tail, this⟩

  fun m =>
    Subtype.Finset.to_Finset_Subtype ⟨m.val.foldr subconfigurations.inner subconfigurations.inner.left_commutative { {} }, foldr_card d m⟩

theorem mem_subconfigurations (m : MultisetOfCard (Finset V) d ) (m' : MultisetOfCard V d) (h : m' ∈ subconfigurations m) :
    ∃ l : { l : List (Finset V) // l.length = d }, (↑l : Multiset (Finset V)) = ↑m ∧ ∀ i : Fin d, m'.val.toList[i] ∈ l.val[i] := by

  sorry


noncomputable def subconfigurations' : MultisetOfCard (Finset V) d → Finset (MultisetOfCard V d) := by
  classical
  exact fun m =>
    { c | ∃ (l₁ : List V) (l₂ : List (Finset V)), Multiset.ofList l₁ = c ∧ Multiset.ofList l₂ = m ∧ ∀ x ∈ l₁.zip l₂, x.1 ∈ x.2 }

theorem subconfigurations_spec : ∀ m : MultisetOfCard (Finset V) d, subconfigurations m = subconfigurations' m := by
  classical
  intro m
  ext x
  constructor
  case mp =>

    sorry
  case mpr =>
    intro h
    rw [subconfigurations', Finset.mem_filter] at h
    obtain ⟨l₁, l₂, h₁, h₂, h⟩ := h.right
    have hl₁ : l₁.length = d := sorry
    have hl₂ : l₂.length = d := sorry

    have inner_lemma : x.val ∈ m.val.foldr subconfigurations.inner subconfigurations.inner.left_commutative { {} } := by
      simp_rw [←h₁, ←h₂, Multiset.coe_foldr]
      induction l₁ generalizing l₂ with
      | nil =>
        rw [←hl₁] at hl₂
        simp at hl₂
        rw [hl₂]
        simp
      | cons head tail ih =>

        sorry

    simp_rw [subconfigurations, Subtype.Finset.to_Finset_Subtype]
    -- TODO: Fix this aesop mess
    rename_i h_1
    simp_all only [Finset.mem_univ, Sym.val_eq_coe, Prod.forall, exists_and_left, true_and, Multiset.empty_eq_zero,
      Finset.mem_map, Finset.mem_attach, Subtype.exists]
    obtain ⟨val, property⟩ := m
    obtain ⟨val_1, property_1⟩ := x
    obtain ⟨w, h_1⟩ := h_1
    obtain ⟨left, right⟩ := h_1
    obtain ⟨w_1, h_1⟩ := right
    obtain ⟨left_1, right⟩ := h_1
    subst property_1
    simp_all only [Sym.coe_mk]
    subst left_1 left
    simp_all only [Multiset.coe_eq_coe, Multiset.coe_foldr, Multiset.coe_card]
    apply Exists.intro
    · apply Exists.intro
      · rfl
      · simp_all only [Multiset.coe_card]


theorem subconfigurations_singleton : ∀ s : MultisetOfCard V d, subconfigurations (s.map singleton) = {s} := by
  have inner_lemma : ∀ s : MultisetOfCard V d, (s.map singleton).val.foldr subconfigurations.inner subconfigurations.inner.left_commutative { {} } = {↑s} := by
    intro s
    apply MultisetOfCard.induction_on s
    · rfl
    · intro a _ s' ih
      simp_rw [MultisetOfCard.map_cons, MultisetOfCard.cons_coe, Multiset.foldr_cons, ih, subconfigurations.inner]
      simp only [Finset.singleton_biUnion]
  intro s
  simp_rw [subconfigurations, inner_lemma]
  rfl

def test_def (a b : ℕ) : a ∆ b

theorem subconfigurations_not_injective : ¬Function.Injective (subconfigurations (V := V) (d := d)) := by
  aesop
  simp

theorem subconfigurations_injective : Function.Injective (subconfigurations (V := V) (d := d)) := by
  -- Not true: Both ({}, {A}) and ({}, {B}) produce {}
  intro a b h
  induction d with
  | zero =>
    simp_rw [MultisetOfCard.card_zero_eq_empty]
  | succ c ih =>


    sorry

def IsMaximized (s : Finset (MultisetOfCard (Finset V) d)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬subconfigurations a ⊆ subconfigurations b

def IsActiveMaximized (π : CondensedBipartiteLCL V a p) : Prop := IsMaximized π.active

def IsPassiveMaximized (π : CondensedBipartiteLCL V a p) : Prop := IsMaximized π.passive

def CondensedBipartiteLCL.toBipartiteLCL (π : CondensedBipartiteLCL V a p) : BipartiteLCL V a p where
  active := π.active.biUnion subconfigurations
  passive := π.passive.biUnion subconfigurations

def BipartiteLCL.toCondensedBipartiteLCL (π : BipartiteLCL V a p) : CondensedBipartiteLCL V a p where
  active := π.active.image (MultisetOfCard.map singleton)
  passive := π.passive.image (MultisetOfCard.map singleton)

theorem BipartiteLCL.toCondensedBipartiteLCL.invertible :
  Function.LeftInverse (@CondensedBipartiteLCL.toBipartiteLCL V _ _ a p) BipartiteLCL.toCondensedBipartiteLCL := by
  intro π
  simp [BipartiteLCL.toCondensedBipartiteLCL, CondensedBipartiteLCL.toBipartiteLCL]
  have {d : ℕ} (s : Finset (MultisetOfCard V d)) : (Finset.image (MultisetOfCard.map singleton) s).biUnion subconfigurations = s := by
    apply Finset.cons_induction_on s (p := (fun s => ((Finset.image (MultisetOfCard.map singleton) s).biUnion subconfigurations = s)))
    rfl
    intro a s' ha h_ind
    simp_rw [Finset.cons_eq_insert, Finset.image_biUnion, Finset.biUnion_insert, Finset.insert_eq, subconfigurations_singleton a, ←Finset.image_biUnion, h_ind]
  congr
  exact this _
  exact this _

-- def IsMaximized (π : CondensedBipartiteLCL V a p) : Prop :=
--   ∀ c ∈ V.passive,
--   sorry

def BipartiteLCL.eliminate_round (π : BipartiteLCL V a p) : BipartiteLCL (Finset V) p a where
  active := { x : MultisetOfCard (Finset V) p | ∀ c ∈ subconfigurations x, c ∈ π.passive }
  passive := { x : MultisetOfCard (Finset V) a | ∃ c ∈ subconfigurations x, c ∈ π.active }


def CondensedBipartiteLCL.eliminate_round (π : CondensedBipartiteLCL V a p) : BipartiteLCL (Finset V) p a where
  active := sorry
  passive := sorry

#eval BipartiteLCL.eliminate_round (SinklessOrientation 3)

-- structure IsSimplerThan (π₁ : BipartiteLCL V a p) (π₂ : BipartiteLCL U a p) where
--   active_map : π₁.active.attach → π₂.active.attach
--   passive_map : π₁.passive.attach → π₂.passive.attach

-- instance : LE

def testMultiset : Multiset (Fin 10) := {1, 2, 2, 3, 3, 3}

#eval testMultiset.powersetCard 3

-- Helper function for `pick`. given a list `l`, `pickAux n l` is the list of
def Multiset.pickAux (n : ℕ) (l : List α) → List (Multiset α) :=
  sorry

def Multiset.pick (m : Multiset V) (n : ℕ) : Multiset V :=

  sorry

def foobar (s : MultisetOfCard α 3) (m : MultisetOfCard s 3) : MultisetOfCard α 3 :=
  let m' : Multiset _ := m.val
  let m' : Multiset α := m'
  sorry


def ZRAlgorithm V U d := Configuration V d → Configuration U d

noncomputable def ZRAlgorithm.coeToConfigs (algo : ZRAlgorithm V U d) (valid : Finset (MultisetOfCard V d)) : Finset (MultisetOfCard U d) :=
  valid.image (fun config =>
    let a : List V := config.val.toList
    have : a.length = d := by aesop
    ⟨Multiset.ofList $ List.ofFn $ algo (this ▸ a.get), by simp⟩
  )

-- instance : Coe (ZRAlgorithm V U d) (Finset (MultisetOfCard V d) → Finset (MultisetOfCard U d)) :=
--   ⟨ZRAlgorithm.coeToConfigs⟩

-- def ZRSolvable (π : BipartiteLCL V a p) : Prop :=
--   ∃ canonical_config ∈ π.active, ∀ passive_config : MultisetOfCard canonical_config.val.toFinset p, passive_config ∈ π.passive

def PossibleForOtherSide (config : Fin d → V) (valid : Finset (MultisetOfCard V d')) : Prop :=
  ∀ p : Fin d, ∃ c ∈ valid, ∃ l ∈ c, config p = l

def ZRReducible (π₁ : BipartiteLCL V a p) (π₂ : BipartiteLCL U a p) : Prop :=
  ∃ algo : ZRAlgorithm V U a,
    ∀ passive_config : Configuration U p,
      PossibleForOtherSide passive_config (algo.coeToConfigs π₁.active) →
      -- (∀ q : Fin p, ∃ active_config : Configuration V a, active_config.toMultiset ∈ π₁.active → ∃ q' : Fin a, algo active_config q' = passive_config q) →
      passive_config.toMultiset ∈ π₂.passive
-- TODO: Not saying that passive configurations preimage is in π₁


  -- ∃ active_map : π₂.active.attach → π₁.active.attach, ∃ passive_map : π₂.passive.attach → π₁.passive.attach,
  --   ∀ passive_config ∈ π₂.passive.attach, ∀ passive_label ∈ passive_config, ∀ active_config ∈ π₂.active.attach,
  --     passive_label ∈ active_config →

def ZRSolvable (π : BipartiteLCL V a p) : Prop := ZRReducible (TrivialLCL Unit a p) π

infixl:1000 " ≤ˡᶜˡ " => ZRReducible

theorem trivial_lcl_is_simplest : ∀ π : BipartiteLCL V a p, ZRReducible π (TrivialLCL Unit a p) := by
  intro π
  use Function.const (Configuration V a) (Function.const (Fin a) ())
  intro passive_config _
  exact Fintype.complete passive_config.toMultiset

theorem empty_lcl_is_hardest : ∀ π : BipartiteLCL V a p, ZRReducible (EmptyLCL Unit a p) π := by
  intro π
  rw [ZRReducible]
  rw [EmptyLCL]
  simp_all [PossibleForOtherSide, ZRAlgorithm.coeToConfigs]
  -- simp only [Finset.not_mem_empty]
  use Function.const
  intro c h
  match p with
  | 0 =>
    rw [Configuration.toMultiset]
    simp
    by_cases h : π.passive = ∅
    rw [h]
    simp
    sorry
    sorry

  | k + 1 =>
    exfalso
    exact h 0
  -- use _
  -- intro passive_config h
  -- exact Fintype.complete passive_config.toMultiset


theorem ZRReducible.refl : ∀ π : BipartiteLCL V a p, ZRReducible π π := sorry

-- def map_unary_trivial_to_binary_trivial : BipartitleLCL Unit 3 3 → BipartiteLCL Boo

-- instance : LE (BipartiteLCL V a p)  := { le := IsSimplerThan }

theorem BipartiteLCL.eliminate_round.is_simpler_than : ∀ π : BipartiteLCL V a p, (π.eliminate_round.swap) ≤ˡᶜˡ π := by

  sorry

-- #eval BipartiteLCL.eliminate_round $ BipartiteLCL.eliminate_round (SinklessOrientation 3)
-- #eval! BipartiteLCL.eliminate_round' $ BipartiteLCL.eliminate_round' (SinklessOrientation 3)

-- example : Repr (Multiset V) := inferInstance


-- Set world

-- structure BipartiteLCL' (a p : ℕ) where
--   active : Set (MultisetOfCard V a)
--   passive : Set (MultisetOfCard V p)

-- def SinklessOrientation' (d : ℕ) : BipartiteLCL' Bool d 2 where
--   active := { s : MultisetOfCard Bool d | true ∈ s }
--   passive := { ⟨{false, true}, by simp⟩ }


-- def subsets' {V : Type*} (m : MultisetOfCard (Set V) p) : Set (MultisetOfCard V p) :=
--   m.prop ▸ m.val.recOn (C := fun d => Set (MultisetOfCard V (Multiset.card d))) ∅ (fun s _ res =>
--     ⋃ e ∈ s, ⋃ r ∈ res, { ⟨e ::ₘ r, by simp⟩ }
--   ) (by
--     sorry
--   )

-- def BipartiteLCL'.eliminate_round (π : BipartiteLCL' V a p) : BipartiteLCL' (Set V) p a where
--   active := { x | ∀ c ∈ subsets' x, c ∈ π.passive }
--   passive := { x | ∃ c ∈ subsets' x, c ∈ π.active }


-- Maximization of a problem:
-- Instead of writing `sets of multisets of labels`, we write `sets of multisets of sets of labels`.
-- Then a constraint exists on the passive side if it can be formed by any choise of labels from sets (see `subconfigurations`).
-- This we call a condensed configuration. This is a way to formalize RE notation: `AB CD CD` = `A C C, A C D, A D C, ...`
-- Usually active side is given in normal form while passive side is given in condensed notation.
--
-- A passive configuration satisfies "universal quantifier" if all of its subconfigurations satisfy passive constraint.
-- To maximize: Collect all sets of multisets of sets of labels that satisfy "universal quantifier", then discard those
-- whose superset is already in the set. This version is called "maximized version of the constraint".

-- Diagram of passive side:
-- L₁ ≤ L₂ := ∀ c : Config ∈ π.passive, let C' be obtained from C by replacing 1
-- (really arbitrarily many, but 1 is enough by transitivity) L₁ with L₂, then C' ∈ π.passive
-- This gives a partial order, and it gives a diagram representation
-- Intuitively: When L₁ ≤ L₂, then any occurence of L₁ can be replaced by L₂.


-- Steps of proof for N, E
-- 1. Proove that the diagram is a specific thing. Prove both that some arrows exist and that non-existent arrows don't exist.
--    Proving this is easy when problem is given in maximized version of the constraint:
--    If some set of config contains L₁, then it also contains L₂.
--    To prove that an arrow does not exist, then there exists a configutation `L₁ A B` such that `L₂ A B` does not exist.
--
-- 2. M(E) (maximized version of E) = E': Every set s of labels in E', if L₁ is in s, then L₂ is also in s. We call this "right-closedness".
--    Then <L₁, L₃> := L₁ + L₂ + successors. This is called "generator({L₁, L₃})".
--    When writing a set, it suffices to write their generators. This is especially useful in writing the active side of the next problem.
--    Intuition: For a fixed point, usually the active side consists of only generators of singleton sets.
-- 2. (for real): Take E and add some additional configurations, call this sum E'. Let E be given as a set of condensed configurations. Proof that E' is maximized.
--    Joonatan's result: To prove maximization, ∀ c₁ c₂ : CondensedConfig ∈ E', ∀ u : Fin d, ∀ perm φ of 1..d, let c := combination of c₁ c₂ w.r.t. u and φ, then c is dominated by E'.
--    "C is dominated by E'": There is a superset of C in E', that is C is in E', or C is not maximal in E'
--    "combination of c₁ c₂ w.r.t. u, φ": see c₁ and c₂ as lists. Then φ represents a matching of c₁ and c₂.
--        At position u, you take (c₁ u ∪ c₂ (φ u)), in other positions you take the intersection.
--
-- 3. E'' := E' + something. "relax, then maximize (re), then relax again".
-- Steps 2. and 3. are called "for all step". Now E'' is new active constraint.
--
-- 4. Σ' := set of all sets of appearing in E''
-- 5. N' := take original node constraints N. Then replace each label with all sets of Σ' that contain that label, and take the product.
--    This is called "existential step".
--
-- Steps 1..5 give one half-step.
-- Applying this half-step twice, then you get N'''' and E''''. Every label is going to looks like <<L₁>, <L₂, L₃>>.
--
-- Improtant observation, for step 2. If if the position u of combination the sets s₁ and s₂ are contained (s₁ ⊆ s₂), then we can ignore that case as it is included in other cases.
--
-- The result of "existential step" is usually huge. There exists a compact way to define them: You can refer to only smallest sets of sets with supersets in the same position,
-- and then say that it generates the supersets.
-- The reason why we do this that we can use generator to get the same result implicitly.
--
-- In this proof it is enough to refer to "renaming reducibility", no "zero-round reducibility" needed.
