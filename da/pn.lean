import Mathlib

structure PNNetwork (V : Type*) where
  degree : V → ℕ
  port : (v : V) → Fin (degree v) → ((u : V) × Fin (degree u))
  port_involutive : Function.Involutive (Sigma.uncurry port)

def PNNetwork.port' {g : PNNetwork V} : (v : V) × Fin (g.degree v) → ((u : V) × Fin (g.degree u)) :=
  Sigma.uncurry g.port

def PNNetwork.Port {g : PNNetwork V} : Type* := (v : V) × Fin (g.degree v)

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
  fun target =>
    fun v =>
      cm.map_preserves_degree _ ▸ target (cm.map v)


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


theorem PNNetwork.doubleCover.is_cover (g : PNNetwork V) : CoveringMap g.doubleCover g where
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
  is_stopping_state : State d → Prop
  init : {d : ℕ} → Input d → State d
  send : {d : ℕ} → State d → Fin d → Msg
  recv : {d : ℕ} → State d → (Fin d → Msg) → State d
  recv_stop_idempotent : ∀ {d : ℕ}, ∀ (state : State d), is_stopping_state state → ∀ (msg : Fin d → Msg), recv state msg = state



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
  ∃ steps, ∀ v, a.is_stopping_state (a.stepOnFor g (a.initOn g input) steps v)

def PNAlgorithm.HaltsOn (a : PNAlgorithm) (g : PNNetwork V) : Prop :=
  ∀ input, a.HaltsOnWith g input

theorem PNAlgorithm.covering_map_indistinguishable.step_on.incoming {g : PNNetwork V} {g' : PNNetwork V'} (a : PNAlgorithm) (cm : CoveringMap g g')
  (state : (v : V') → a.State (g'.degree v)) :
  ∀ (v : V), stepOn.incoming a g' state (cm.map v) = cm.map_preserves_degree v ▸ stepOn.incoming a g (cm.expandState state) v := by
  intro v
  reduce
  rw [eqRec_eq_cast, cast_eq_iff_heq.mpr]
  apply Function.hfunext
  · rw [cm.map_preserves_degree v]

  · intro p q h_pq

    have ⟨b, c⟩ := cm.map_preserves_connections v p
    simp_all

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
  reduce
  repeat rw [eqRec_eq_cast]
  rw [cast_eq_iff_heq]
  congr
  · exact (cm.map_preserves_degree v).symm
  · symm
    apply cast_heq

def NodeLabeling {V : Type*} (S : Type*) := V → S

-- structure ColoringOn (c : ℕ) (g : PNNetwork V) where
--   labeling : NodeLabeling (Fin c)
--   is_coloring := ∀ e ∈ g.edges, labeling e.1 ≠ labeling e.2

-- def EdgeLabeling {V : Type*} (S : Type*) := V → S

-- def PNAlgorithm.bipartiteMatching : PNAlgorithm where
--   Input := ColoringOn

-- partial def PNAlgorithm.evalOn.loop (a : PNAlgorithm) (g : PNNetwork V) (state : (v : V) → a.State (g.degree v)) : (v : V) → a.State (g.degree v) := by
--   by_cases ∀ (v : V), a.is_stopping_state (state v)
--   · exact state
--   · exact loop a g (a.stepOn g state)

-- noncomputable def PNAlgorithm.evalOn (a : PNAlgorithm) (g : PNNetwork V) (input : (v : V) → a.Input (g.degree v)) : (v : V) → a.State (g.degree v) :=
--   -- let rec loop (state : (v : V) → a.State (g.degree v)) : (v : V) → a.State (g.degree v) := by
--   --   by_cases ∀ (v : V), a.is_stopping_state (state v)
--   --   · exact state
--   --   · exact loop (a.stepOn g state)
--   sorry

-- def PNAlgorithm.evalOnFor (a : PNAlgorithm) (g : PNNetwork V) (input : (v : V) → a.Input (g.degree v)) : (v : V) → a.State (g.degree v) :=

-- theorem PNAlgorithm.double_cover
