import HwFormal.TransSys

/-- Finite execution trace, newest step first.
Each entry is `(state, input applied at that state)`. -/
inductive Trace (sys : TransSys S I O) : List (S × I) → Prop where
  | nil : Trace sys []
  | singleton : ∀ (s : S) (i : I),
      sys.Init s i → sys.Constraint s i → Trace sys [(s, i)]
  | cons : ∀ (s s' : S) (i i' : I) (t : List (S × I)),
      Trace sys ((s, i) :: t) → sys.Trans s s' i → sys.Constraint s' i' →
      Trace sys ((s', i') :: (s, i) :: t)

def trace_safe (sys : TransSys S I O) : Prop :=
  ∀ (t : List (S × I)), Trace sys t → ∀ p ∈ t, ¬ sys.Bad p.1 p.2

namespace Trace

variable {sys : TransSys S I O}

/-- Every entry of a trace heads a (suffix) trace. -/
theorem suffix_of_mem {t : List (S × I)} (h : Trace sys t) {p : S × I} (hp : p ∈ t) :
    ∃ t', Trace sys (p :: t') := by
  induction h with
  | nil => simp at hp
  | singleton s i hi hc => simp at hp; subst hp; exact ⟨[], .singleton s i hi hc⟩
  | cons s s' i i' t ht htr hc ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, .cons s s' i i' t ht htr hc⟩
    · exact ih hp

end Trace

/-- `run` only depends on the inputs up to the current step. -/
theorem TransSys.run_congr (sys : TransSys S I O) (o : O) {inp inp' : Nat → I} (k : Nat)
    (h : ∀ j ≤ k, inp j = inp' j) : sys.run o inp k = sys.run o inp' k := by
  induction k with
  | zero => simp [TransSys.run, h 0 (Nat.le_refl 0)]
  | succ k ih =>
    simp only [TransSys.run]
    rw [ih (fun j hj => h j (by omega)), h k (by omega)]

namespace Trace

variable {sys : TransSys S I O}

/-- The head of a trace of length `n+1` is the `n`-th state of some valid run. -/
theorem head_run {t : List (S × I)} (h : Trace sys t) :
    ∀ s i t', t = (s, i) :: t' →
      ∃ o inp, sys.validUpTo o inp t'.length ∧ sys.run o inp t'.length = s ∧ inp t'.length = i := by
  induction h with
  | nil => intro _ _ _ h; cases h
  | singleton s i hi hc =>
    intro s₀ i₀ t' heq
    simp only [List.cons.injEq, Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    obtain ⟨o, ho⟩ := hi
    refine ⟨o, fun _ => i, ?_, ho, rfl⟩
    intro k hk
    simp at hk; subst hk
    simpa [TransSys.Constraint, TransSys.run, ho] using hc
  | cons s s' i i' t _ htr hc ih =>
    intro s₀ i₀ t' heq
    simp only [List.cons.injEq, Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    obtain ⟨o, inp, hv, hr, hi⟩ := ih s i t rfl
    let inp' : Nat → I := fun k => if k = t.length + 1 then i' else inp k
    have hagree : ∀ k ≤ t.length, sys.run o inp k = sys.run o inp' k := fun k hk =>
      sys.run_congr o k (fun j hj => by simp [inp']; omega)
    refine ⟨o, inp', ?_, ?_, by simp [inp']⟩
    · intro k hk
      by_cases hkn : k = t.length + 1
      · subst hkn
        simp only [List.length_cons] at *
        have : sys.run o inp' (t.length + 1) = s' := by
          simp only [TransSys.run]
          rw [← hagree _ (Nat.le_refl _)]
          simp [inp', hr, hi]
          exact htr
        simpa [TransSys.Constraint, this, inp'] using hc
      · have hk' : k ≤ t.length := by simp at hk; omega
        rw [← hagree k hk']
        simpa [inp', hkn] using hv k hk'
    · simp only [List.length_cons, TransSys.run]
      rw [← hagree _ (Nat.le_refl _)]
      simp [inp', hr, hi]
      exact htr

end Trace

/-- The trace of the first `n+1` steps of a run, newest first. -/
def TransSys.runTrace (sys : TransSys S I O) (o : O) (inp : Nat → I) : Nat → List (S × I)
  | 0 => [(sys.run o inp 0, inp 0)]
  | n + 1 => (sys.run o inp (n + 1), inp (n + 1)) :: sys.runTrace o inp n

theorem TransSys.trace_runTrace (sys : TransSys S I O) (o : O) (inp : Nat → I) (n : Nat)
    (hv : sys.validUpTo o inp n) : Trace sys (sys.runTrace o inp n) := by
  induction n with
  | zero => exact .singleton _ _ ⟨o, rfl⟩ (hv 0 (Nat.le_refl 0))
  | succ n ih =>
    have ih' := ih (fun k hk => hv k (by omega))
    cases n with
    | zero => exact .cons _ _ _ _ [] ih' rfl (hv 1 (Nat.le_refl 1))
    | succ n => exact .cons _ _ _ _ _ ih' rfl (hv _ (Nat.le_refl _))

theorem trace_safe_iff_safe (sys : TransSys S I O) : trace_safe sys ↔ sys.safe := by
  constructor
  · intro hts o inp n hv
    have hmem : (sys.run o inp n, inp n) ∈ sys.runTrace o inp n := by
      cases n <;> simp [TransSys.runTrace]
    have := hts _ (sys.trace_runTrace o inp n hv) _ hmem
    simpa [TransSys.Bad] using this
  · intro hs t ht p hp
    obtain ⟨t', ht'⟩ := ht.suffix_of_mem hp
    obtain ⟨o, inp, hv, hr, hi⟩ := ht'.head_run p.1 p.2 t' rfl
    have := hs o inp t'.length hv
    simp [TransSys.Bad, ← hr, ← hi, this]
