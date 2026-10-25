-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepDefs.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/PrepDefs.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepFrames

/-!
# The objects of one preparation sample

`PrepData` collects an old known sample of one scale class (old blocks of length
`2^-(T+s)`), the class scales, the frame parameters and the analytic masks `Good`.
From it we build (paper Lemma 3.5, part 1, lines 918-1157):

* the frames: the keys of x0661's `FramePackage` for the fitting matrices `Qf`;
* the entries: pairs `(b, i)` of an old chart and a frame listed by it (`valid`);
* the source sets `S`: the old chart's incidences on its half-open old block, for the
  entry of its own frame, empty for witness-only entries;
* the pair masks `H`: a source incidence, a second time in the coarse block where the
  trajectory is a selected incidence of the witness chart, inside `Good`, with the witness
  derivative floor at the source time;
* the lists `lst'`: the entries of the charts listed by the old lists;
* the equations `P κ`: the old tests in the frame's base coordinates.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open MeasureTheory Set MvPolynomial Submission.Lib.K4VelocityStrips

/-- The data of one preparation sample. -/
structure PrepData where
  W : ℕ
  T : ℕ
  s : ℕ
  C : ℕ
  γ : Fin C → Fin W
  j : Fin C → Fin (2 ^ (T + s))
  c : Fin C → EuclideanSpace ℝ (Fin 2)
  u : Fin C → EuclideanSpace ℝ (Fin 2)
  Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ
  R : Fin C → MvPolynomial (Fin 4) ℝ
  A : Fin C → Set (ℕ × (Fin 6 → ℝ))
  F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)
  B : Fin W → ℝ
  Good : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  iso : Bool
  R₁ : ℝ
  R₂ : ℝ
  g : ℝ
  κ₀ : ℝ
  Kb : ℕ
  dfl : ℝ

namespace PrepData

variable (D : PrepData)

/-- The fitting matrices. -/
noncomputable def Qf (b : Fin D.C) : Matrix (Fin 2) (Fin 2) ℝ := fitMat (D.iso = true) D.R₁ (D.Q b)

noncomputable def S₁ : ℝ := 2 ^ D.s * D.R₁

noncomputable def S₂ : ℝ := 2 ^ D.s * max (fitR₂ (D.iso = true) D.R₁ D.R₂) (D.g * D.R₁)

/-- The frame dilation. -/
noncomputable def Afr : ℝ := 2 * (78 * (4 * D.κ₀)) + 2

noncomputable def keys : Finset (FrKey D.W D.T) := frameKeys D.γ D.j D.c D.u D.Qf D.g D.S₁ D.S₂

/-- The number of frames. -/
noncomputable def J : ℕ := D.keys.card

/-- The enumeration of the frames. -/
noncomputable def key (i : Fin D.J) : FrKey D.W D.T := (D.keys.equivFin.symm i : FrKey D.W D.T)

/-- The frame key of an old chart. -/
noncomputable def src (b : Fin D.C) : FrKey D.W D.T := srcKey D.γ D.j D.c D.u D.Qf D.g D.S₁ D.S₂ b

/-- The frames listed by an old chart: its own and the compatible ones. -/
noncomputable def compat (b : Fin D.C) : Finset (FrKey D.W D.T) :=
  insert (D.src b) (compatKeys D.γ D.j D.c D.u D.Qf D.g D.S₁ D.S₂ D.Kb b)

/-- The entries. -/
noncomputable def valid : Finset (Fin D.C × Fin D.J) := by
  classical
  exact Finset.univ.filter (fun bi => D.key bi.2 ∈ D.compat bi.1)

/-- The number of entries. -/
noncomputable def m : ℕ := D.valid.card

noncomputable def ent (s : Fin D.m) : Fin D.C × Fin D.J := (D.valid.equivFin.symm s : Fin D.C × Fin D.J)

/-- The old chart of an entry. -/
noncomputable def chartOf (s : Fin D.m) : Fin D.C := (D.ent s).1

/-- The frame of an entry. -/
noncomputable def frame (s : Fin D.m) : Fin D.J := (D.ent s).2

/-- Frame data. -/
noncomputable def fγ (i : Fin D.J) : Fin D.W := (D.key i).1

noncomputable def fj (i : Fin D.J) : Fin (2 ^ D.T) := (D.key i).2.1

noncomputable def fc (i : Fin D.J) : EuclideanSpace ℝ (Fin 2) := keyC D.g D.S₁ D.S₂ (D.key i)

noncomputable def fu (i : Fin D.J) : EuclideanSpace ℝ (Fin 2) := keyU D.g D.S₁ D.S₂ (D.key i)

noncomputable def fQ (i : Fin D.J) : Matrix (Fin 2) (Fin 2) ℝ := keyQ D.g D.S₁ D.S₂ D.Afr (D.key i)

/-- The closed coarse block. -/
noncomputable def blk (J₀ : Fin (2 ^ D.T)) : Set ℝ :=
  Icc (((J₀ : ℕ) : ℝ) / (2 : ℝ) ^ D.T) ((((J₀ : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T)

/-- The source incidences of an old chart: its selected incidences on the half-open
old block. -/
def Sb (b : Fin D.C) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  D.F b ∩ {p | p.2 < (((D.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s)}

/-- The source set of an entry. -/
noncomputable def S (s : Fin D.m) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := by
  classical
  exact if D.key (D.frame s) = D.src (D.chartOf s) then D.Sb (D.chartOf s) else ∅

/-- The pair mask of a source entry and a witness entry. -/
def H (s s' : Fin D.m) : Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) :=
  {p | D.key (D.frame s) = D.src (D.chartOf s) ∧ D.frame s' = D.frame s ∧
    (p.1, p.2.1) ∈ D.Sb (D.chartOf s) ∧ p.2.2 ∈ D.blk (D.fj (D.frame s)) ∧
    (p.1, p.2.2) ∈ D.Sb (D.chartOf s') ∧ (p.1, p.2.1) ∈ D.Good (D.γ (D.chartOf s)) ∧
    D.dfl * D.B (D.γ (D.chartOf s)) ≤
      |eval (x p.1 p.2.1) (pderiv 3 (D.R (D.chartOf s')))|}

/-- The new lists. -/
noncomputable def lst' (γ₀ : Fin D.W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : Finset (Fin D.m) := by
  classical
  exact Finset.univ.filter (fun s => D.chartOf s ∈ D.lst γ₀ o)

/-- The equations: old tests in the frame's base coordinates. -/
noncomputable def P (κ : ℝ) (s : Fin D.m) : MvPolynomial (Fin 4) ℝ :=
  transport D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.B (D.fγ (D.frame s))) (D.fc (D.frame s))
    (D.fu (D.frame s)) (D.fQ (D.frame s)) (D.R (D.chartOf s))

/-! ### Basic facts -/

theorem key_injective : Function.Injective D.key := by
  intro i i' h
  have := Subtype.ext h
  exact D.keys.equivFin.symm.injective this

theorem key_mem (i : Fin D.J) : D.key i ∈ D.keys := (D.keys.equivFin.symm i).2

theorem src_mem_keys (b : Fin D.C) : D.src b ∈ D.keys := srcKey_mem _ _ _ _ _ _ _ _ b

theorem exists_key_eq {k : FrKey D.W D.T} (hk : k ∈ D.keys) : ∃ i, D.key i = k :=
  ⟨D.keys.equivFin ⟨k, hk⟩, by simp [key]⟩

theorem ent_mem (s : Fin D.m) : D.ent s ∈ D.valid := (D.valid.equivFin.symm s).2

theorem ent_injective : Function.Injective D.ent := by
  intro s s' h
  exact D.valid.equivFin.symm.injective (Subtype.ext h)

theorem key_frame_mem_compat (s : Fin D.m) : D.key (D.frame s) ∈ D.compat (D.chartOf s) := by
  classical
  have h := D.ent_mem s
  simp only [valid, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

theorem src_world (b : Fin D.C) : (D.src b).1 = D.γ b := rfl

theorem src_block (b : Fin D.C) : (D.src b).2.1 = coarseIdx (D.j b) := rfl

/-- Every frame listed by a chart is in its world and coarse block. -/
theorem compat_world_block {b : Fin D.C} {k : FrKey D.W D.T} (hk : k ∈ D.compat b) :
    k.1 = D.γ b ∧ k.2.1 = coarseIdx (D.j b) := by
  classical
  unfold compat at hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact ⟨rfl, rfl⟩
  · unfold compatKeys at hk
    rw [Finset.mem_filter] at hk
    exact ⟨hk.2.1, hk.2.2.1⟩

theorem frame_world (s : Fin D.m) : D.fγ (D.frame s) = D.γ (D.chartOf s) :=
  (D.compat_world_block (D.key_frame_mem_compat s)).1

theorem frame_block (s : Fin D.m) : D.fj (D.frame s) = coarseIdx (D.j (D.chartOf s)) :=
  (D.compat_world_block (D.key_frame_mem_compat s)).2

theorem compat_mem_keys {b : Fin D.C} {k : FrKey D.W D.T} (hk : k ∈ D.compat b) : k ∈ D.keys := by
  classical
  unfold compat at hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact D.src_mem_keys b
  · unfold compatKeys at hk
    exact (Finset.mem_filter.mp hk).1

/-- The entry of a chart and a frame it lists. -/
noncomputable def entOf (b : Fin D.C) (i : Fin D.J) (h : D.key i ∈ D.compat b) : Fin D.m := by
  classical
  exact D.valid.equivFin ⟨(b, i), by
    simp only [valid, Finset.mem_filter, Finset.mem_univ, true_and]; exact h⟩

theorem ent_entOf (b : Fin D.C) (i : Fin D.J) (h : D.key i ∈ D.compat b) :
    D.ent (D.entOf b i h) = (b, i) := by
  classical
  simp [ent, entOf]

theorem chartOf_entOf (b : Fin D.C) (i : Fin D.J) (h : D.key i ∈ D.compat b) :
    D.chartOf (D.entOf b i h) = b := by
  rw [chartOf, ent_entOf]

theorem frame_entOf (b : Fin D.C) (i : Fin D.J) (h : D.key i ∈ D.compat b) :
    D.frame (D.entOf b i h) = i := by
  rw [frame, ent_entOf]

/-- The frame index of a chart's own key. -/
noncomputable def srcIdx (b : Fin D.C) : Fin D.J := (D.exists_key_eq (D.src_mem_keys b)).choose

theorem key_srcIdx (b : Fin D.C) : D.key (D.srcIdx b) = D.src b :=
  (D.exists_key_eq (D.src_mem_keys b)).choose_spec

theorem src_mem_compat (b : Fin D.C) : D.src b ∈ D.compat b := by
  classical
  exact Finset.mem_insert_self _ _

/-- The source entry of an old chart. -/
noncomputable def srcEnt (b : Fin D.C) : Fin D.m :=
  D.entOf b (D.srcIdx b) (by rw [D.key_srcIdx]; exact D.src_mem_compat b)

theorem chartOf_srcEnt (b : Fin D.C) : D.chartOf (D.srcEnt b) = b := D.chartOf_entOf _ _ _

theorem frame_srcEnt (b : Fin D.C) : D.frame (D.srcEnt b) = D.srcIdx b := D.frame_entOf _ _ _

theorem srcEnt_injective : Function.Injective D.srcEnt := by
  intro b b' h
  have := congrArg D.chartOf h
  rwa [D.chartOf_srcEnt, D.chartOf_srcEnt] at this

/-- A source entry is the source entry of its chart. -/
theorem eq_srcEnt {s : Fin D.m} (hs : D.key (D.frame s) = D.src (D.chartOf s)) :
    s = D.srcEnt (D.chartOf s) := by
  apply D.ent_injective
  have h1 : D.frame s = D.srcIdx (D.chartOf s) :=
    D.key_injective (by rw [hs, D.key_srcIdx])
  rw [srcEnt, D.ent_entOf]
  exact Prod.ext rfl h1

end PrepData

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
