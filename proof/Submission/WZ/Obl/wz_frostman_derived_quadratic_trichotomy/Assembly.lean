-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Assembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CanonicalFamily
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatExit
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Orientation
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.StickyBranch
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Regularize

/-!
# Assembly of the derived trichotomy, stage A: the canonical setup

From an admissible, individually dense, Frostman family, x0318's `exists_canonical_family`
(copied in `X318/`) and `antipode_free_class` give a canonical subfamily (each tube starts at the
entry of its chord into `B(0, 1-δ)`, so `x' = leftStart δ x' v'`) without antipodal directions,
keeping a `1/(6(D+1))` share, with each shading keeping half of its measure in its canonical tube,
half-overlap, and the Frostman count transferred with a factor `48³`.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

open MeasureTheory

theorem canonical_setup : ∃ D : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ η M : ℝ,
    ∀ (n : ℕ) (x v : Fin n → Sp) (Y : Fin n → Set Sp), 0 < n → (∀ i, ‖v i‖ = 1) →
    (∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1) →
    (∀ i j, i ≠ j → volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩
        Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤
      (1 / 2 : ENNReal) * volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) →
    (∀ i, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) →
    (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
    (∀ W : Set Sp, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℝ) ≤
        ENNReal.ofReal M * volume W) →
    ∃ (k : ℕ) (g : Fin k → Fin n) (x' v' : Fin k → Sp) (S₀ : Finset (Fin k)),
      Function.Injective g ∧ S₀.Nonempty ∧ (n : ℝ) ≤ 6 * (D + 1) * S₀.card ∧
      (∀ j, ‖v' j‖ = 1) ∧ (∀ j, x' j = leftStart δ (x' j) (v' j)) ∧
      (∀ j, Metric.thickening δ (segment ℝ (x' j) (x' j + v' j)) ⊆ Metric.ball (0 : Sp) 1) ∧
      (∀ i j, i ≠ j → volume (Metric.thickening δ (segment ℝ (x' i) (x' i + v' i)) ∩
          Metric.thickening δ (segment ℝ (x' j) (x' j + v' j))) ≤
        (1 / 2 : ENNReal) * volume (Metric.thickening δ (segment ℝ (x' i) (x' i + v' i)))) ∧
      (∀ i ∈ S₀, ∀ j ∈ S₀, 1 ≤ ‖v' i + v' j‖) ∧
      (∀ j, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤
        2 * volume (Y (g j) ∩ Metric.thickening δ (segment ℝ (x' j) (x' j + v' j)))) ∧
      (∀ W : Set Sp, Convex ℝ W →
        ENNReal.ofReal (Set.ncard {j | Metric.thickening δ (segment ℝ (x' j) (x' j + v' j)) ⊆ W} : ℝ) ≤
          ENNReal.ofReal (48 ^ 3 * M) * volume W) := by
  obtain ⟨D, hD⟩ := X318.exists_canonical_family
  refine ⟨D, ?_⟩
  intro δ hδ hδ1 η M n x v Y hn hv hball hov hYT hdens hFrost
  obtain ⟨k, g, x', v', hg, hnk, hv', hnorm, hball', hdist, hhalf, hconv, -⟩ :=
    hD δ hδ hδ1 n x v Y hv hball hov hYT
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hnk; omega
    · exact h
  have hU : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hkpos⟩, Finset.mem_univ _⟩
  obtain ⟨S₀, -, hS₀ne, hS₀card, hanti⟩ := antipode_free_class v' hv' Finset.univ hU
  refine ⟨k, g, x', v', S₀, hg, hS₀ne, ?_, hv', fun j => ?_, hball', hdist, hanti,
    fun j => ?_, hconv M hFrost⟩
  · have h1 : (n : ℝ) ≤ (D + 1) * k := by exact_mod_cast hnk
    have h2 : ((Finset.univ : Finset (Fin k)).card : ℝ) = k := by simp
    rw [h2] at hS₀card
    have hD0 : (0 : ℝ) ≤ D + 1 := by positivity
    calc (n : ℝ) ≤ (D + 1) * k := h1
      _ ≤ (D + 1) * (6 * S₀.card) := by gcongr
      _ = 6 * (D + 1) * S₀.card := by ring
  · exact eq_leftStart_of_norm hδ (hv' j) (hball' j) (hnorm j)
  · exact (hdens (g j)).trans (hhalf j)

/-- `LongFactor` does not depend on the enumeration of the family. -/
theorem longFactor_reindex {ν δ a b : ℝ} {n n' : ℕ} (A : Fin n → Set Sp) (σ : Fin n' ≃ Fin n)
    (h : X318.LongFactor ν δ a b A) : X318.LongFactor ν δ a b (fun i => A (σ i)) := by
  obtain ⟨k, g, hg, hk, hsize, c, hc, hKT, p, W, hshape, hcov, hdeg, hsat⟩ := h
  have hnn : n' = n := by simpa using Fintype.card_congr σ
  refine ⟨k, fun i => σ.symm (g i), fun i j hij => hg (σ.symm.injective hij), hk, ?_, c, hc,
    ?_, p, W, hshape, ?_, ?_, ?_⟩
  · rw [hnn]; exact hsize
  · simpa only [Equiv.apply_symm_apply] using hKT
  · intro i; simpa only [Equiv.apply_symm_apply] using hcov i
  · intro i; simpa only [Equiv.apply_symm_apply] using hdeg i
  · intro j; simpa only [Equiv.apply_symm_apply] using hsat j

open Classical in
/-- The flat exit from whole flat cells at one level. `B` is a union of whole cells (radius `ρ`)
of a canonical set `S` with a common class; each cell of `B` carries fibre_dichotomy's FLAT
certificate. Then x0318's `flat_exit` gives frozen SC for a subfamily of `B` of size at least
`δ^θ |B|`. -/
theorem flat_exit_of_cells {δ ρ ν Λ ζ ζ₂ ζ₃ θ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν)
    (hζ : 0 ≤ ζ) (hζ₂ : 0 ≤ ζ₂) (hδρ : 2 * δ ≤ ρ) (hρ : ρ ≤ 1 / 10000)
    (hΛ : 16 * δ ^ (-ν - ζ₂ / 200) ≤ Λ) (h64 : 64 * δ ^ ν ≤ 1)
    (herror : X318.localFlatLoss * δ ^ (ζ₃ - ζ - 5 * (2 * ν)) ≤ 1)
    (hretain : 2 * δ ^ (θ - 2 * ν) ≤ 1)
    {m : ℕ} (x v : Fin m → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (S : Finset (Fin m)) (hS : S.Nonempty)
    (hcls : ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 ρ (x i) (v i) = classKey 200000 ρ (x i') (v i'))
    (B : Finset (Fin m)) (hBS : B ⊆ S) (hBne : B.Nonempty)
    (hwhole : ∀ i ∈ B, ∀ j ∈ S, lineCell (ρ / 20) (x j) (v j) = lineCell (ρ / 20) (x i) (v i) →
      j ∈ B)
    (hcert : ∀ i ∈ B, ∃ a b : ℝ, δ ≤ a ∧ Λ * a < b ∧ b ≤ 2 ∧
      X318.LongFactor ν δ a b (fun j : Fin (fibre S (fun i => lineCell (ρ / 20) (x i) (v i)) i).card =>
        Metric.thickening δ (segment ℝ
          (x ((fibre S (fun i => lineCell (ρ / 20) (x i) (v i)) i).equivFin.symm j))
          (x ((fibre S (fun i => lineCell (ρ / 20) (x i) (v i)) i).equivFin.symm j) +
            v ((fibre S (fun i => lineCell (ρ / 20) (x i) (v i)) i).equivFin.symm j)))))
    (hFB : ∀ W : Set Sp, Convex ℝ W →
      ENNReal.ofReal ((B.filter (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card : ℝ) ≤
        ENNReal.ofReal (δ ^ (-ζ) * B.card) * volume W)
    (hpig : (((Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
        (Nat.log 2 ⌊(B.card : ℝ) * δ ^ (-ν)⌋₊ + 1) : ℕ) : ℝ) ≤ δ ^ (-ν)) :
    ∃ (k : ℕ) (g : Fin k → Fin m), Function.Injective g ∧ (∀ j, g j ∈ B) ∧
      δ ^ θ * B.card ≤ k ∧
      X318.FlatPrisms ζ₂ ζ₃ δ (fun j => Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j)))) := by
  classical
  set κ : Fin m → (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun i => lineCell (ρ / 20) (x i) (v i) with hκdef
  -- the parents: the exact cover of `S` at radius `ρ`
  obtain ⟨q, -, z, w, hw, hov, hexu, -, hfib⟩ :=
    cell_cover hδ hδρ hρ x v hv hT hcan hanti S hS hcls
  -- the family of `B`
  set nB := B.card with hnB
  let eB : Fin nB ≃ B := B.equivFin.symm
  set xB : Fin nB → Sp := fun j => x (eB j) with hxB
  set vB : Fin nB → Sp := fun j => v (eB j) with hvB
  have heBS : ∀ j, (eB j : Fin m) ∈ S := fun j => hBS (eB j).2
  let par : Fin nB → Fin q := fun j => (hexu (eB j) (heBS j)).choose
  have hpar : ∀ j, Metric.thickening δ (segment ℝ (xB j) (xB j + vB j)) ⊆
      Metric.thickening ρ (segment ℝ (z (par j)) (z (par j) + w (par j))) :=
    fun j => (hexu (eB j) (heBS j)).choose_spec.1
  have huniq : ∀ j l, Metric.thickening δ (segment ℝ (xB j) (xB j + vB j)) ⊆
      Metric.thickening ρ (segment ℝ (z l) (z l + w l)) → l = par j :=
    fun j l h => (hexu (eB j) (heBS j)).choose_spec.2 l h
  have hnBpos : 0 < nB := Finset.card_pos.2 hBne
  -- Frostman of the `B`-family
  have hFrostB : X318.Frostman (δ ^ (-ζ)) (fun j => X318.Tube δ (xB j) (vB j)) := by
    intro W hW
    have hcnt : Set.ncard {j : Fin nB | X318.Tube δ (xB j) (vB j) ⊆ W} =
        (B.filter (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card :=
      ncard_enum B (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)
    rw [hcnt]
    exact hFB W hW
  -- the FLAT certificates of the parents' fibres
  have hflat : ∀ l, (Finset.univ.filter (fun j => par j = l)).Nonempty → ∃ a b : ℝ,
      δ ≤ a ∧ Λ * a < b ∧ b ≤ 2 ∧
      X318.LongFactor ν δ a b (fun j : Fin (Finset.univ.filter (fun j => par j = l)).card =>
        X318.Tube δ (xB ((Finset.univ.filter (fun j => par j = l)).equivFin.symm j))
          (vB ((Finset.univ.filter (fun j => par j = l)).equivFin.symm j))) := by
    intro l hl
    obtain ⟨j₀, hj₀⟩ := hl
    have hj₀l : par j₀ = l := (Finset.mem_filter.1 hj₀).2
    set i₀ : Fin m := (eB j₀).1 with hi₀
    have hi₀B : i₀ ∈ B := (eB j₀).2
    obtain ⟨a, b, hδa, hab, hb2, hLF⟩ := hcert i₀ hi₀B
    refine ⟨a, b, hδa, hab, hb2, ?_⟩
    set P := Finset.univ.filter (fun j => par j = l) with hP
    set F := fibre S κ i₀ with hF
    -- `par j = l` iff the tube of `eB j` is in the cell of `i₀`
    obtain ⟨i₁, hi₁, -, -, hiff⟩ := hfib l
    have hpar_iff : ∀ j, par j = l ↔ κ (eB j) = κ i₀ := by
      intro j
      have h0 : κ i₀ = κ i₁ := by
        have := (hiff i₀ (hBS hi₀B)).1 (hj₀l ▸ hpar j₀)
        exact this
      constructor
      · intro hjl
        have := (hiff (eB j) (heBS j)).1 (hjl ▸ hpar j)
        exact this.trans h0.symm
      · intro hc
        have hsub : Metric.thickening δ (segment ℝ (xB j) (xB j + vB j)) ⊆
            Metric.thickening ρ (segment ℝ (z l) (z l + w l)) :=
          (hiff (eB j) (heBS j)).2 (hc.trans h0)
        exact (huniq j l hsub).symm
    -- the map `P → F`
    have hmemF : ∀ t : Fin P.card, (eB (P.equivFin.symm t) : Fin m) ∈ F := by
      intro t
      have ht := (P.equivFin.symm t).2
      have hpl : par (P.equivFin.symm t) = l := (Finset.mem_filter.1 ht).2
      exact Finset.mem_filter.2 ⟨heBS _, (hpar_iff _).1 hpl⟩
    let φ : Fin P.card → Fin F.card := fun t => F.equivFin ⟨eB (P.equivFin.symm t), hmemF t⟩
    have hφinj : Function.Injective φ := by
      intro t t' h
      have h1 := F.equivFin.injective h
      have h2 : (eB (P.equivFin.symm t)).1 = (eB (P.equivFin.symm t')).1 := by
        have := congrArg (fun z : {i // i ∈ F} => z.1) h1
        exact this
      have h3 : eB (P.equivFin.symm t) = eB (P.equivFin.symm t') := Subtype.ext h2
      have h4 : ((P.equivFin.symm t : Fin nB)) = (P.equivFin.symm t' : Fin nB) := eB.injective h3
      exact P.equivFin.symm.injective (Subtype.ext h4)
    have hφsurj : Function.Surjective φ := by
      intro u
      set f := F.equivFin.symm u with hf
      have hfF : (f : Fin m) ∈ F := f.2
      obtain ⟨hfS, hfc⟩ := Finset.mem_filter.1 hfF
      have hfB : (f : Fin m) ∈ B := hwhole i₀ hi₀B f hfS hfc
      set j := eB.symm ⟨f, hfB⟩ with hj
      have hjP : j ∈ P := by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (hpar_iff j).2 ?_⟩
        simp only [hj, Equiv.apply_symm_apply]
        exact hfc
      refine ⟨P.equivFin ⟨j, hjP⟩, ?_⟩
      have e3 : (⟨(eB (P.equivFin.symm (P.equivFin ⟨j, hjP⟩)) : Fin m),
          hmemF (P.equivFin ⟨j, hjP⟩)⟩ : F) = f := by
        apply Subtype.ext
        simp only [Equiv.symm_apply_apply, hj, Equiv.apply_symm_apply]
      calc φ (P.equivFin ⟨j, hjP⟩) = F.equivFin f := congrArg F.equivFin e3
        _ = u := by rw [hf, Equiv.apply_symm_apply]
    let σ : Fin P.card ≃ Fin F.card := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
    have hre := longFactor_reindex _ σ hLF
    have hfun : (fun j : Fin P.card => X318.Tube δ (xB (P.equivFin.symm j)) (vB (P.equivFin.symm j))) =
        (fun j => Metric.thickening δ (segment ℝ (x ↑(F.equivFin.symm (σ j)))
          (x ↑(F.equivFin.symm (σ j)) + v ↑(F.equivFin.symm (σ j))))) := by
      funext j
      have hσj : F.equivFin.symm (σ j) = ⟨eB (P.equivFin.symm j), hmemF j⟩ := by
        show F.equivFin.symm (φ j) = _
        simp only [φ, Equiv.symm_apply_apply]
      rw [hσj]
      rfl
    rw [hfun]
    exact hre
  -- apply `flat_exit`
  have hρ8 : ρ ≤ 1 / 8 := by linarith
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨k, g', hg', hk, hFP⟩ := X318.flat_exit hδ hδ1 hν hζ hζ₂ hρ0 hρ8 hΛ h64 hnBpos hpig
    herror hretain xB vB (fun j => hv _) (fun j => hT _) hFrostB z w hw hov par hpar huniq hflat
  refine ⟨k, fun j => eB (g' j), fun j j' h => hg' (eB.injective (Subtype.ext h)),
    fun j => (eB (g' j)).2, hk, hFP⟩

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
