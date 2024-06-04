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
  fun vp =>
    let up := g.port' vp
    let u' := cm.map up.fst
    ⟨u', cm.map_preserves_degree _ ▸ up.snd⟩

-- def CoveringMap.expandState {S : Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') : (V' → S) → (V → S) :=
--   fun target => target ∘ cm.map

abbrev CoveringMap.expandState {S : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') : ((v : V') → S (g'.degree v)) → ((v : V) → S (g.degree v)) :=
  fun target =>
    fun v =>
      cm.map_preserves_degree _ ▸ target (cm.map v)

theorem CoveringMap.expandState.foo {S : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') (state : (v : V') → S (g'.degree v)) :
  ∀ (v : V), cm.expandState state v = cm.map_preserves_degree _ ▸ state (cm.map v) := by simp

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
  Input : ℕ → Type*
  State : ℕ → Type*
  Msg : Type*
  is_stopping_state : State d → Prop
  init : {d : ℕ} → Input d → State d
  send : {d : ℕ} → State d → Fin d → Msg
  recv : {d : ℕ} → State d → (Fin d → Msg) → State d
  recv_stop_idempotent : ∀ {d : ℕ}, ∀ (state : State d), is_stopping_state state → ∀ (msg : Fin d → Msg), recv state msg = state



def PNAlgorithm.initOn (a : PNAlgorithm) (g : PNNetwork V) (input : (v : V) → a.Input (g.degree v)) : (v : V) → a.State (g.degree v) :=
  fun v => a.init (input v)

def PNAlgorithm.stepOn (a : PNAlgorithm) (g : PNNetwork V) (state : (v : V) → a.State (g.degree v)) : (v : V) → a.State (g.degree v) :=
  fun v =>
    -- Collect messages from neighbors
    let incoming (p : Fin (g.degree v)) :=
      let ⟨u, q⟩ := g.port v p
      a.send (state u) q
    a.recv (state v) incoming

def PNAlgorithm.stepOnFor (a : PNAlgorithm) (g : PNNetwork V) (state : (v : V) → a.State (g.degree v)) (steps : ℕ) : (v : V) → a.State (g.degree v) :=
  match steps with
  | 0 => state
  | n + 1 => stepOnFor a g (stepOn a g state) n

def PNAlgorithm.HaltsOnWith (a : PNAlgorithm) (g : PNNetwork V) (input : (v : V) → a.Input (g.degree v)) : Prop :=
  ∃ steps, ∀ v, a.is_stopping_state (a.stepOnFor g (a.initOn g input) steps v)

def PNAlgorithm.HaltsOn (a : PNAlgorithm) (g : PNNetwork V) : Prop :=
  ∀ input, a.HaltsOnWith g input


theorem PNAlgorithm.covering_map_indistinguishable.step_on {g : PNNetwork V} {g' : PNNetwork V'} (a : PNAlgorithm) (cm : CoveringMap g g') (state : (v : V') → a.State (g'.degree v)) :
  cm.expandState (a.stepOn g' state) = a.stepOn g (cm.expandState state) := by
  let estate := cm.expandState state

  have send_same : ∀ (v : V), a.send (state (cm.map v)) = cm.map_preserves_degree _ ▸ a.send (cm.expandState state v) := by
    intro v
    funext p
    -- have lemma1 (α : Sort*) (β : Sort*) (γ : Sort*) (f : {δ : Type} → δ → γ) : α = β → HEq (@f α) (@f β) := by sorry
    let m₁ := a.send (state (cm.map v))
    let m₂ := a.send (cm.expandState state v)
    let m₃ := cm.map_preserves_degree _ ▸ m₂
    have : HEq m₂ m₃ := by
      aesop
    have : m₁ = m₃ := by
      funext p
      let foo := m₃ p
      reduce
      -- have _ := lemma1 (Fin $ g.degree v) (Fin $ g'.degree (cm.map v))
      -- aesop

      sorry

    -- let m₂ :=  ▸ m₂
    rw [CoveringMap.expandState.foo]
    -- rw [CoveringMap.expandState]

    conv =>
      rhs
      simp

    sorry

  funext v
  -- let lhs := cm.expandState (a.stepOn g' state) v
  -- reduce at lhs


  -- repeat rw [CoveringMap.expandState, PNAlgorithm.stepOn]
  conv =>
    lhs
    rw [CoveringMap.expandState]
    rw [PNAlgorithm.stepOn]
    -- reduce
    lhs


  conv =>
    rhs
    rw [PNAlgorithm.stepOn]
    -- arg 3
    -- rw [CoveringMap.expandState]
    -- reduce
  reduce

  sorry

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
