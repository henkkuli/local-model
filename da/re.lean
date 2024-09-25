import Mathlib

abbrev MultisetOfCard (V : Type*) (c : ℕ) := { s : Multiset V // Multiset.card s = c}

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

structure BipartiteLCL (V : Type u) (a p : ℕ) where
  active : Finset (MultisetOfCard V a)
  passive : Finset (MultisetOfCard V p)
-- deriving Repr

unsafe instance BipartiteLCL.instRepr [Repr V] : Repr (BipartiteLCL V a p) where
reprPrec := fun π _ =>
  let active := Std.Format.text "active: " ++ Repr.reprPrec π.active 0
  let passive := Std.Format.text "passive: " ++ Repr.reprPrec π.passive 0
  .join [active, .line, passive]

def SinklessOrientation (d : ℕ) : BipartiteLCL Bool d 2 where
  active := { s : MultisetOfCard Bool d | true ∈ s }
  passive := { ⟨{false, true}, by simp⟩ }


#eval! SinklessOrientation 5


variable {V : Type*} [instfin : Fintype V] [DecidableEq V]

variable [Repr V] [DecidableEq V] [Fintype V]

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

def transposeFinset' : Multiset (Finset V) → Finset (Multiset V) :=
  let inner : Finset V → Finset (Multiset V) → Finset (Multiset V) :=
    fun next prev =>
      next.biUnion fun a =>
        prev.biUnion fun b =>
          { a ::ₘ b }

  have inner_commutative : LeftCommutative (α := Finset V) inner := by
    intro a b rest
    unfold_let inner
    beta_reduce
    conv =>
      lhs
      arg 2
      ext
      rw [Finset.biUnion_biUnion]
      arg 2
      ext
      rw [Finset.biUnion]
      simp
      rw [Multiset.toFinset]
      arg 1
      rw [Multiset.dedup_map_dedup_eq]
      arg 1
      simp
      arg 1
      ext
      rw [Multiset.cons_swap]

    conv =>
      rhs
      arg 2
      ext
      rw [Finset.biUnion_biUnion]
      arg 2
      ext
      rw [Finset.biUnion]
      simp
      rw [Multiset.toFinset]
      arg 1
      rw [Multiset.dedup_map_dedup_eq]
      arg 1
      simp

    rw [Finset.biUnion_comm]


  Multiset.foldr inner inner_commutative { {} }

def Subtype.Finset.to_Finset_Subtype {p : α → Prop} : { s : Finset α // ∀ e ∈ s, p e } → Finset { e : α // p e } :=
  fun ⟨m, h⟩  =>
    let f : { s : α // s ∈ m } ↪ { e : α // p e } := {
      toFun := fun ⟨e, h'⟩ => ⟨e, h e h'⟩
      inj' := by
        intro a b h
        rename_i x h_1
        simp only [Subtype.mk.injEq] at h
        rw [Subtype.mk.injEq]
        assumption
    }
    m.attach.map f

def subconfigurations : MultisetOfCard (Finset V) d → Finset (MultisetOfCard V d) :=
  let inner : Finset V → Finset (Multiset V) → Finset (Multiset V) :=
    fun next prev =>
      next.biUnion fun a =>
        prev.biUnion fun b =>
          { a ::ₘ b }

  have inner_commutative : LeftCommutative (α := Finset V) inner := by
    intro a b rest
    unfold_let inner
    beta_reduce
    conv =>
      lhs
      arg 2
      ext
      rw [Finset.biUnion_biUnion]
      arg 2
      ext
      rw [Finset.biUnion]
      simp
      rw [Multiset.toFinset]
      arg 1
      rw [Multiset.dedup_map_dedup_eq]
      arg 1
      simp
      arg 1
      ext
      rw [Multiset.cons_swap]

    conv =>
      rhs
      arg 2
      ext
      rw [Finset.biUnion_biUnion]
      arg 2
      ext
      rw [Finset.biUnion]
      simp
      rw [Multiset.toFinset]
      arg 1
      rw [Multiset.dedup_map_dedup_eq]
      arg 1
      simp

    rw [Finset.biUnion_comm]

  have inner_card (d : ℕ) : ∀ next prev, (∀ e ∈ prev, Multiset.card e = d) → ∀ e ∈ inner next prev, Multiset.card e = d + 1 := by
    intro next prev h e h_e
    unfold_let inner at h_e
    rw [@Finset.mem_biUnion] at h_e
    obtain ⟨n, h_n, h_p⟩ := h_e
    rw [@Finset.mem_biUnion] at h_p
    obtain ⟨s, h_s, h_e⟩ := h_p
    rw [Multiset.mem_singleton.mp h_e, ←h s h_s]
    exact Multiset.card_cons _ _

  have foldr_card (d : ℕ) (moc : MultisetOfCard (Finset V) d) : ∀ e ∈ moc.val.foldr inner inner_commutative { {} }, Multiset.card e = d := by
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
        apply inner_card
        have foo := ih ⟨tail, this⟩
        rw [←Multiset.coe_foldr inner inner_commutative]
        exact foo

  fun m =>
    Subtype.Finset.to_Finset_Subtype ⟨m.val.foldr inner inner_commutative { {} }, foldr_card d m⟩



def BipartiteLCL.eliminate_round (π : BipartiteLCL V a p) : BipartiteLCL (Finset V) p a where
  active := { x : MultisetOfCard (Finset V) p | ∀ c ∈ subconfigurations x, c ∈ π.passive }
  passive := { x : MultisetOfCard (Finset V) a | ∃ c ∈ subconfigurations x, c ∈ π.active }



#eval BipartiteLCL.eliminate_round (SinklessOrientation 3)

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
