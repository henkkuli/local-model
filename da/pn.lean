import Mathlib

notation a " ≈ " b => HEq a b

structure PNNetwork (V : Type*) where
  degree : V → ℕ
  port : (v : V) → Fin (degree v) → ((u : V) × Fin (degree u))
  port_involutive : Function.Involutive (Sigma.uncurry port)

def PNNetwork.port' {g : PNNetwork V} : (v : V) × Fin (g.degree v) → ((u : V) × Fin (g.degree u)) :=
  Sigma.uncurry g.port

def PNNetwork.Port {g : PNNetwork V} : Type* := (v : V) × Fin (g.degree v)

-- def PNNetwork.ports (g : PNNetwork V) (v : V) : List g.Port := sorry

def PNNetwork.coe_SimpleGraph (g : PNNetwork V) : SimpleGraph V where
  Adj := fun v u => v ≠ u ∧ ∃ (p : Fin (g.degree v)), (g.port v p).fst = u
  symm := by
    intro v u h
    constructor
    · exact h.left.symm
    · have ⟨p, h⟩ := h.right
      rw [←h]
      let q := (g.port v p).snd
      apply Exists.intro q
      have := congrArg Sigma.fst (g.port_involutive ⟨v, p⟩)
      assumption

instance PNNetwork.instCoeSimpleGraph : Coe (PNNetwork V) (SimpleGraph V) where
  coe := PNNetwork.coe_SimpleGraph

-- theorem (l : List α) (a : α) (h : α ∈ l) : (l.findIdx)

theorem PNNetwork.coe_SimpleGraph_surjective {V : Type*} [inst : Fintype V] : Function.Surjective (PNNetwork.coe_SimpleGraph (V := V)) := by
  classical
  intro g

  let vertices : List V := inst.elems.toList
  let neighbours : V → List V := fun v => (g.neighborFinset v).toList
  have h_neighbours (v : V) : (neighbours v).length = g.degree v := by
    rw [Finset.length_toList, SimpleGraph.card_neighborFinset_eq_degree]
  let degree := fun v ↦ g.degree v
  let port : (v : V) → (Fin (degree v)) → ((u : V) × (Fin (degree u)))  := fun v p ↦
      let u := (neighbours v)[p]'(by simp[h_neighbours])
      have h_uv_adj : g.Adj u v := by
        apply g.adj_symm
        apply (g.mem_neighborFinset v u).mp
        have := List.get_mem (neighbours v) p (by simp[h_neighbours])
        simp_all only [Finset.mem_toList, getElem_fin, List.getElem_eq_get, neighbours, u]

      let q := (neighbours u).findIdx (fun v' => v' = v)
      have : q < g.degree u := by
        rw [← h_neighbours]
        apply List.findIdx_lt_length.mpr
        simp_all only [Finset.mem_toList, SimpleGraph.mem_neighborFinset, decide_eq_true_eq, exists_eq_right, neighbours]

      let q : Fin (g.degree u) := ⟨q, this⟩
      ⟨u, q⟩

  let pnn : PNNetwork V := {
    degree := degree
    port := port
    port_involutive := by
      intro vp
      -- repeat rw [Sigma.uncurry]
      have : ∀ u, (neighbours u).Nodup := sorry
      let uq := port vp.fst vp.snd
      let vp' := port uq.fst uq.snd
      have : vp'.fst = vp.fst := by
        reduce
        have := List.find
        sorry

      -- have : HEq p' p := sorry
      have : vp' = vp := by sorry
      rw [Sigma.uncurry, Sigma.uncurry]
      -- aesop?


      -- let v' :=
      sorry
      -- simp_all

  }
  use pnn
  sorry

-- def SimpleGraph.coe_pn_network (g : SimpleGraph V) : PNNetwork V where
--   degree := sorry
--   port := sorry
--   port_involutive := sorry

-- def PNNetwork.cycle (c : ℕ) : PNNetwork (Fin c) where
--   degree := Function.const _ 2
--   port := fun v (p : Fin 2) =>
--     have deg2 : degree _ v = 2 := sorry
--     match p with
--     | 0 => (v, deg2 ▸ 1)
--     | 1 => (v, 0)
--   port_involutive := sorry

theorem foobar' [DecidableEq α] (l : List α) (a : α) (h : a ∈ l) : l.findIdx (fun b => a = b) < l.length := by
  apply List.findIdx_lt_length_of_exists
  use a
  constructor <;> simp only [h, decide_True]

theorem foobar [DecidableEq α] (l : List α) (a : α) (h : a ∈ l) : l.get ⟨(l.findIdx (fun b => a = b)), by simp [foobar', h]⟩ = a := by
  let p := fun b => decide (a = b)
  -- have : Function.Injective p := by sorry
  -- apply this


  sorry

def PNNetwork.neighborSet (g : PNNetwork V) (v : V) : Set V :=
  {u : V | ∃ p, (g.port v p).fst = u}

-- instance PNNetwork.neighborSet.memDecidable (g : PNNetwork V) (v : V) : DecidablePred (· ∈ g.neighborSet v) :=

structure CoveringMap (g : PNNetwork V) (f : PNNetwork U) where
  map : V → U
  map_surj : Function.Surjective map
  map_preserves_degree : ∀ (v : V), g.degree v = f.degree (map v)
  map_preserves_connections : ∀ (v : V), (p : Fin (g.degree v)) →
    let ⟨v', p'⟩ := g.port v p
    let ⟨u', q'⟩ := f.port (map v) (map_preserves_degree v ▸ p)
    map v' = u' ∧ HEq p' q'

def CoveringMap.mapPort (cm : CoveringMap g f) : g.Port → f.Port :=
  fun vp => ⟨cm.map vp.fst, cm.map_preserves_degree _ ▸ vp.snd⟩


-- def CoveringMap.expandState {S : Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') : (V' → S) → (V → S) :=
--   fun target => target ∘ cm.map

abbrev CoveringMap.expandState {S : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') : ((v : V') → S (g'.degree v)) → ((v : V) → S (g.degree v)) :=
  fun state =>
    fun v =>
      cm.map_preserves_degree _ ▸ state (cm.map v)


-- abbrev CoveringMap.expandState' {S : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') : ((v : V') → S (g'.degree v)) → ((v : V) → S (g'.degree (cm.map v))) :=
--   fun target =>
--     fun v =>
--       cm.map_preserves_degree _ ▸ target (cm.map v)

-- theorem CoveringMap.expandState_eq_expandState' {S : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') (state : (v : V') → S (g'.degree v)): cm.expandState state = cast (cm.map_preserves_degree _) cm.expandState' state := sorry

theorem CoveringMap.expandState.foo {S : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') (state : (v : V') → S (g'.degree v)) :
  ∀ (v : V), cm.expandState state v = cm.map_preserves_degree _ ▸ state (cm.map v) := by simp


-- theorem CoveringMap.expandState.preserves_functions {S : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') (state : (v : V') → S (g'.degree v)) (f : {d : ℕ} → S d → U) :
--   ∀ (v : V), f (state (cm.map v)) = f (cm.expandState state v) := by
--   intro v
--   congr
--   exact (cm.map_preserves_degree v).symm
--   simp

-- theorem CoveringMap.expandState'.preserves_functions {S S' : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') (state : (v : V') → S (g'.degree v)) (f : {d : ℕ} → S d → S' d) :
--   ∀ (v : V), f (state (cm.map v)) = f (cm.expandState' state v) := by
--   intro v
--   congr
--   rw [expandState', eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]

def PNNetwork.doubleCover (g : PNNetwork V) : PNNetwork (V × Bool) where
  degree := fun ⟨v, _⟩ => g.degree v
  port := fun ⟨v, layer⟩ => fun p =>
    let ⟨u, q⟩ := g.port v p
    ⟨(u, ¬layer), q⟩
  port_involutive := by
    intro ⟨⟨v, layer⟩, p⟩
    repeat rw [Sigma.uncurry]
    simp

    have base := g.port_involutive ⟨v, p⟩

    constructor
    · exact congrArg Sigma.fst base
    · reduce at base
      rw [base]

def PNNetwork.doubleCover.is_cover (g : PNNetwork V) : CoveringMap g.doubleCover g where
  map := fun ⟨v, _⟩ => v
  map_surj := by
    intro v
    aesop
  map_preserves_degree := by
    aesop
  map_preserves_connections := by
    aesop


structure PNAlgorithm where
  Input : ℕ → Sort*
  State : ℕ → Sort*
  Msg : Sort*
  IsStoppingState : State d → Prop
  init : {d : ℕ} → Input d → State d
  send : {d : ℕ} → State d → Fin d → Msg
  recv : {d : ℕ} → State d → (Fin d → Msg) → State d
  recv_stop_idempotent : ∀ {d : ℕ}, ∀ (state : State d), IsStoppingState state → ∀ (msg : Fin d → Msg), recv state msg = state



def PNAlgorithm.initOn (a : PNAlgorithm) (g : PNNetwork V) (input : (v : V) → a.Input (g.degree v)) : (v : V) → a.State (g.degree v) :=
  fun v => a.init (input v)


abbrev PNAlgorithm.stepOn.incoming (a : PNAlgorithm) (g : PNNetwork V) (state : (v : V) → a.State (g.degree v)) : (v : V) → Fin (g.degree v) → a.Msg :=
  fun v p =>
    -- Collect messages from neighbors
    let ⟨u, q⟩ := g.port v p
    a.send (state u) q

def PNAlgorithm.stepOn (a : PNAlgorithm) (g : PNNetwork V) (state : (v : V) → a.State (g.degree v)) : (v : V) → a.State (g.degree v) :=
  fun v =>
    a.recv (state v) (stepOn.incoming a g state v)

def PNAlgorithm.stepOnFor (a : PNAlgorithm) (g : PNNetwork V) (state : (v : V) → a.State (g.degree v)) (steps : ℕ) : (v : V) → a.State (g.degree v) :=
  match steps with
  | 0 => state
  | n + 1 => stepOnFor a g (stepOn a g state) n

def PNAlgorithm.HaltsOnWith (a : PNAlgorithm) (g : PNNetwork V) (input : (v : V) → a.Input (g.degree v)) : Prop :=
  ∃ steps, ∀ v, a.IsStoppingState (a.stepOnFor g (a.initOn g input) steps v)

def PNAlgorithm.HaltsOn (a : PNAlgorithm) (g : PNNetwork V) : Prop :=
  ∀ input, a.HaltsOnWith g input

theorem PNAlgorithm.covering_map_indistinguishable.step_on.incoming {g : PNNetwork V} {g' : PNNetwork V'} (a : PNAlgorithm) (cm : CoveringMap g g')
  (state : (v : V') → a.State (g'.degree v)) :
  ∀ (v : V), stepOn.incoming a g' state (cm.map v) = cm.map_preserves_degree v ▸ stepOn.incoming a g (cm.expandState state) v := by
  intro v
  reduce
  rw [eqRec_eq_cast, cast_eq_iff_heq.mpr]
  apply Function.hfunext
  · congr
    exact cm.map_preserves_degree v

  · intro p q h_pq

    have ⟨b, c⟩ := cm.map_preserves_connections v p

    congr
    · rw [cm.map_preserves_degree, b]
      congr
      rw [eqRec_eq_cast, cast_eq_iff_heq]
      assumption

    · have := congr_arg_heq state b
      rw [rec_heq_iff_heq]
      apply HEq.trans this
      congr
      rw [eqRec_eq_cast, cast_eq_iff_heq]
      assumption

    · apply HEq.trans c
      rw [eqRec_eq_cast]
      congr
      rw [cast_eq_iff_heq.mpr]
      assumption

theorem PNAlgorithm.covering_map_indistinguishable.step_on {g : PNNetwork V} {g' : PNNetwork V'} (a : PNAlgorithm) (cm : CoveringMap g g') (state : (v : V') → a.State (g'.degree v)) :
  cm.expandState (a.stepOn g' state) = a.stepOn g (cm.expandState state) := by
  funext v
  reduce
  repeat rw [eqRec_eq_cast]
  rw [cast_eq_iff_heq]
  congr
  · exact (cm.map_preserves_degree v).symm
  · symm
    apply cast_heq
  · have h := covering_map_indistinguishable.step_on.incoming a cm state v
    reduce at h
    simp_all only [eqRec_heq_iff_heq, heq_eq_eq]


theorem PNAlgorithm.covering_map_indistinguishable.init_on {g : PNNetwork V} {g' : PNNetwork V'} (a : PNAlgorithm) (cm : CoveringMap g g') (input : (v : V') → a.Input (g'.degree v)) :
  cm.expandState (a.initOn g' input) = a.initOn g (cm.expandState input) := by
  funext v
  simp [CoveringMap.expandState, initOn]
  simp [eqRec_eq_cast]
  rw [cast_eq_iff_heq]
  congr
  · exact (cm.map_preserves_degree v).symm
  · symm
    apply cast_heq

def PortLabeling {V : Type*} (L : Type*) (g : PNNetwork V) := g.Port → L


def NodeLabeling {V : Type*} (L : Type*) (g : PNNetwork V) := V → L


structure Coloring {V : Type*} (c : ℕ) (g : PNNetwork V) where
  color : NodeLabeling (Fin c) g
  proper : ∀ (v : V), ∀ (p : Fin (g.degree v)), color v ≠ color (g.port v p).fst

def Coloring.to_higher {V : Type*} (c : ℕ) (g : PNNetwork V) (d : ℕ) {h : d ≥ c} (col : Coloring c g) : Coloring d g where
  color := fun v => (col.color v).castLE h
  proper := by
    intro v p h_contra
    apply col.proper
    exact Fin.castLE_inj.mp h_contra


def ColeVishkin.ldb {k : ℕ} (a b : Fin (2 ^ (k + 1))) : Fin (k + 1) :=
  match k with
  | 0 => 0
  | k' + 1 =>
    let (a_div, a_bit) : Fin (2^(k' + 1)) × Fin 2 := (a.divNat, a.modNat)
    let (b_div, b_bit) : Fin (2^(k' + 1)) × Fin 2 := (b.divNat, b.modNat)
    if a_bit = b_bit then
      let r := @ColeVishkin.ldb k' a_div b_div
      r + 1
    else
      0

theorem ColeVishkin.ldb.symm {k : ℕ} (a b : Fin (2 ^ (k + 1))) : ColeVishkin.ldb a b = ColeVishkin.ldb b a := by
  induction k with
  | zero => rfl
  | succ k' h =>
    unfold ColeVishkin.ldb
    aesop

example : @ColeVishkin.ldb 0 0 1 = 0 := by rfl
example : @ColeVishkin.ldb 10 0 4 = 2 := by rfl
example : @ColeVishkin.ldb 10 5 4 = 0 := by rfl



def ColeVishkin.ldb' {k : ℕ} (a b : Fin (2 ^ (k + 1))) {h : a ≠ b} : Fin (k + 1) :=
  match k with
  | 0 => 0
  | k' + 1 =>

    let a_div : Fin (2^(k' + 1)) := a.divNat
    let a_bit : Fin 2 := a.modNat
    let b_div : Fin (2^(k' + 1)) := b.divNat
    let b_bit : Fin 2 := b.modNat

    if h_bit : a_bit = b_bit then
      -- Condition for induction
      have : a_div ≠ b_div := by
        intro h_div

        have : (a_div, a_bit) = (b_div, b_bit) := by
          simp_all [a_bit, b_bit, a_div, b_div]
        have := congrArg finProdFinEquiv this

        have a' : a = finProdFinEquiv (a_div, a_bit) := by
          apply finProdFinEquiv.symm.injective
          simp [finProdFinEquiv_symm_apply a]
        have b' : b = finProdFinEquiv (b_div, b_bit) := by
          apply finProdFinEquiv.symm.injective
          simp [finProdFinEquiv_symm_apply b]
        apply h
        rw [a', b', this]

      let r := @ColeVishkin.ldb' k' a_div b_div this
      r + 1
    else
      0

theorem ColeVishkin.ldb'.bit_differs {k : ℕ} (a b : Fin (2 ^ (k + 1))) {h : a ≠ b} : (BitVec.ofFin a).getLsb (@ColeVishkin.ldb' k a b h) ≠ (BitVec.ofFin b).getLsb (@ColeVishkin.ldb' k a b h) := by
  intro h_contra
  induction k with
  | zero =>
    apply h
    rw [←BitVec.ofFin.injEq]
    apply BitVec.eq_of_getLsb_eq
    intro i
    match i with
    | 0 => apply h_contra
  | succ k' h_k =>

    sorry

-- def ColeVishkin.lowest_differing_bit {k : ℕ} (a b : Fin (2 ^ k)) {h : a ≠ b}: Fin k.succ :=
--   match k with
--   | 0 => 0
--   | k + 1 =>
--     if a.val.bodd ≠ b.val.bodd then
--       0
--     else
--       let (a_div, a_bit) := (a.divNat, a.modNat)
--       let (b_div, b_bit) := (b.divNat, b.modNat)
--       if h_bit : a_bit = b_bit then
--         have h_div : a_div ≠ b_div := by
--           intro h_contra
--           simp_all
--           let a' := finProdFinEquiv (a_div, a_bit)
--           let b' := finProdFinEquiv (b_div, b_bit)
--           have : a = a' := by aesop
--           have : a' = b' := by
--             rename_i k_1
--             aesop_subst [h_bit, h_contra]
--             simp_all only [Nat.add_eq, Nat.add_zero, Nat.pow_eq, a',b']

--           apply h
--           apply?
--           sorry
--           -- sorry
--       -- let c := @lowest_differing_bit k (@Fin.divNat 2 _ a) (@Fin.divNat 2 _ b) (by apply?)
--         sorry
--       else
--         0
  -- match a with
  -- | ⟨a,b⟩ => sorry
  -- let a := BitVec.ofFin a
  -- let b := BitVec.ofFin b
  -- let h : a ≠ b := by simp_all only [ne_eq, BitVec.ofFin.injEq, not_false_eq_true, a, b]


-- def ColeVishkin.reduction {k : ℕ} (a b : Fin (2 ^ k)) {h : a ≠ b}: Fin (2 * k) :=
--   let a := BitVec.ofFin a
--   let b := BitVec.ofFin b
--   let h : a ≠ b := by simp_all only [ne_eq, BitVec.ofFin.injEq, not_false_eq_true, a, b]
--   -- have := @BitVec.eq_of_getLsb_eq _ a b
--   have := not_forall.mp $ h ∘ BitVec.eq_of_getLsb_eq
--   let i := this.choose
--   match a.getLsb i with
--   | ⊥ => Fin.castLE (Nat.le_mul_of_pos_left _ (by simp)) i
--   | ⊤ => Fin.castLE (Nat.le_mul_of_pos_left _ (by simp)) i

-- theorem ColeVishkin.reduction.preserves_coloring {k : ℕ} (a b : Fin (2 ^ k)) :
--   ∀ (c : Fin (2 ^ k)), a ≠ b → b ≠ c → ColeVishkin.reduction a b ≠ ColeVishkin.reduction b c := by sorry


-- theorem PNAlgorithm.cannot_color_cycles : ¬∃ (a : PNAlgorithm), ∀ (g : PNNetwork V),

-- Labeling problem is a set of valid labeling for each graph.
-- def LabelingProblem {V L : Type*} := ∀ (g : PNNetwork V), Set (LabelingOf g)

-- structure LCLProblem

-- def NodeLabeling {V : Type*} (S : Type*) := V → S

-- structure ColoringOn (c : ℕ) (g : PNNetwork V) where
--   labeling : NodeLabeling (Fin c)
--   is_coloring := ∀ e ∈ g.edges, labeling e.1 ≠ labeling e.2

-- def EdgeLabeling {V : Type*} (S : Type*) := V → S

-- def PNAlgorithm.bipartiteMatching : PNAlgorithm where
--   Input := ColoringOn

-- partial def PNAlgorithm.evalOn.loop (a : PNAlgorithm) (g : PNNetwork V) (state : (v : V) → a.State (g.degree v)) : (v : V) → a.State (g.degree v) := by
--   by_cases ∀ (v : V), a.IsStoppingState (state v)
--   · exact state
--   · exact loop a g (a.stepOn g state)

-- noncomputable def PNAlgorithm.evalOn (a : PNAlgorithm) (g : PNNetwork V) (input : (v : V) → a.Input (g.degree v)) : (v : V) → a.State (g.degree v) :=
--   -- let rec loop (state : (v : V) → a.State (g.degree v)) : (v : V) → a.State (g.degree v) := by
--   --   by_cases ∀ (v : V), a.IsStoppingState (state v)
--   --   · exact state
--   --   · exact loop (a.stepOn g state)
--   sorry

-- def PNAlgorithm.evalOnFor (a : PNAlgorithm) (g : PNNetwork V) (input : (v : V) → a.Input (g.degree v)) : (v : V) → a.State (g.degree v) :=

-- theorem PNAlgorithm.double_cover

def PNLabeling (⅀ : Type*) (g : PNNetwork V) := g.Port → ⅀

def PNLabeling.IsNodeLabeling {⅀ : Type*} {g : PNNetwork V} (L : PNLabeling ⅀ g) : Prop :=
  ∀ v : V, ∃ l : ⅀, ∀ p : Fin (g.degree v), L ⟨v, p⟩ = l


def PNProblem := {V U : Type*} → (g : PNNetwork V) → (l : V → U) → Prop

def PNColoring (d : Nat) : PNProblem := fun g l => ∀ v, ∀ u ∈ g.neighborSet v, l u ≠ l v
