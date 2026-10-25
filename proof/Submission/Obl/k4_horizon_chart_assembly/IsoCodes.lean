import Submission.Obl.k4_horizon_chart_assembly.HeavyCells

/-!
# Kernel code tables on an isotropic fine mesh

With the isotropic world mesh `ρ = q/D` and the group normalization radius `R q` (`R ≥ 1`
real), the time code of a normalized incidence is exactly the world time bin shifted by `jD`,
and each planar code is `⌊(c - Dσ)/R⌋` or one more, where `c` is the world planar bin. So every
world cell meets at most four normalized codes of a group.
-/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped ENNReal BigOperators

noncomputable section

/-- The normalized codes of group `(j, σ)` met by the world cell `Z`. -/
def isoCodes (D : ℕ) (R : ℝ) (j : ℕ) (σ : Fin 2 → ℤ) (Z : (Fin 3 → ℤ) × ℤ) :
    Finset (ℤ × (Fin 2 → ℤ)) :=
  (Finset.univ : Finset (Fin 2 → Fin 2)).image (fun ε =>
    (Z.1 0 - (j : ℤ) * D, fun k => ⌊((Z.1 k.succ : ℝ) - D * σ k) / R⌋ + (ε k : ℤ)))

theorem isoCodes_card_le (D : ℕ) (R : ℝ) (j : ℕ) (σ : Fin 2 → ℤ) (Z : (Fin 3 → ℤ) × ℤ) :
    (isoCodes D R j σ Z).card ≤ 4 := by
  apply Finset.card_image_le.trans
  simp

/-- A real number in `[c, c + 1)`, shifted and divided by `R ≥ 1`, has floor `f` or `f + 1`,
where `f` is the floor for `c` itself. -/
theorem floor_div_mem {x c d R : ℝ} (hR : 1 ≤ R) (hc : c ≤ x) (hc' : x < c + 1) :
    ∃ ε : Fin 2, ⌊(x - d) / R⌋ = ⌊(c - d) / R⌋ + (ε : ℤ) := by
  have hR0 : 0 < R := by linarith
  have hlo : ⌊(c - d) / R⌋ ≤ ⌊(x - d) / R⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hR0.le)
  have hhi : ⌊(x - d) / R⌋ ≤ ⌊(c - d) / R⌋ + 1 := by
    have h1 : (x - d) / R < (c - d) / R + 1 := by
      rw [div_add_one hR0.ne', div_lt_div_iff_of_pos_right hR0]
      linarith
    have h2 := Int.lt_floor_add_one ((c - d) / R)
    have h3 : (x - d) / R < ((⌊(c - d) / R⌋ + 1 + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    have h4 := Int.floor_lt.mpr h3
    omega
  rcases (show ⌊(x - d) / R⌋ = ⌊(c - d) / R⌋ ∨ ⌊(x - d) / R⌋ = ⌊(c - d) / R⌋ + 1 by omega)
    with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

/-- The kernel code of a normalized incidence of group `(j, Γ)` lies among the codes met by the
world cell of the lifted incidence. -/
theorem normalized_code_mem_isoCodes (B a : ℝ) {q R : ℝ} (hq : 0 < q) (hR : 1 ≤ R)
    {D : ℕ} (hD : 0 < D) (j : ℕ) (Γ : (Fin 2 → ℤ) × ℤ) (p : Incidence) :
    (⌊p.2 * (D : ℝ)⌋, fun k : Fin 2 => ⌊(D : ℝ) *
      (groupIntercept q a ((j : ℝ) * q) (R * q) Γ p.1 +
        p.2 • groupVelocity q (R * q) p.1) k⌋) ∈
      isoCodes D R j Γ.1 (worldCell (q / D) (q / D) B a (timeLift ((j : ℝ) * q) q p)) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hR0 : 0 < R := by linarith
  -- the time code
  have htime : ⌊p.2 * (D : ℝ)⌋ =
      (worldCell (q / D) (q / D) B a (timeLift ((j : ℝ) * q) q p)).1 0 - (j : ℤ) * D := by
    have h : graphPoint p.1 ((j : ℝ) * q + q * p.2) (Fin.castSucc 0) /
        cellScale (q / D) (q / D) 0 = ((j * D : ℤ) : ℝ) + p.2 * D := by
      simp only [graphPoint, cellScale]
      push_cast
      field_simp
    simp only [worldCell, timeLift]
    rw [h, Int.floor_intCast_add]
    ring
  -- the planar codes
  have hspace : ∀ k : Fin 2, ∃ ε : Fin 2,
      ⌊(D : ℝ) * (groupIntercept q a ((j : ℝ) * q) (R * q) Γ p.1 +
        p.2 • groupVelocity q (R * q) p.1) k⌋ =
      ⌊(((worldCell (q / D) (q / D) B a (timeLift ((j : ℝ) * q) q p)).1 k.succ : ℝ) -
        D * Γ.1 k) / R⌋ + (ε : ℤ) := by
    intro k
    set y := graphPoint p.1 ((j : ℝ) * q + q * p.2) k.succ.castSucc with hy
    have hcell : (worldCell (q / D) (q / D) B a (timeLift ((j : ℝ) * q) q p)).1 k.succ =
        ⌊y / (q / D)⌋ := by
      simp only [worldCell, timeLift, hy]
      fin_cases k <;> rfl
    have hval : (D : ℝ) * (groupIntercept q a ((j : ℝ) * q) (R * q) Γ p.1 +
        p.2 • groupVelocity q (R * q) p.1) k = (y / (q / D) - D * Γ.1 k) / R := by
      rw [hy]
      fin_cases k <;>
      · simp [graphPoint, groupIntercept, groupVelocity, normalizedBlockIntercept,
          normalizedBlockVelocity, midpointGroupCenter, planarPoint, planarVelocity]
        field_simp
        ring
    rw [hval, hcell]
    exact floor_div_mem hR (Int.floor_le _) (Int.lt_floor_add_one _)
  choose ε hε using hspace
  apply Finset.mem_image.mpr
  refine ⟨ε, Finset.mem_univ _, ?_⟩
  rw [htime]
  congr 1
  funext k
  rw [hε k]

/-- The kernel's code table for one group: all codes met by the heavy cells it visits. -/
def isoKernelCodes (S : Set ((Fin 3 → ℤ) × ℤ)) (vis : (Fin 3 → ℤ) × ℤ → Prop)
    (codes : (Fin 3 → ℤ) × ℤ → Finset (ℤ × (Fin 2 → ℤ))) : Finset (ℤ × (Fin 2 → ℤ)) := by
  classical
  exact if h : S.Finite then (h.toFinset.filter vis).biUnion codes else ∅

theorem mem_isoKernelCodes {S : Set ((Fin 3 → ℤ) × ℤ)} (hS : S.Finite)
    {vis : (Fin 3 → ℤ) × ℤ → Prop} {codes : (Fin 3 → ℤ) × ℤ → Finset (ℤ × (Fin 2 → ℤ))}
    {Z : (Fin 3 → ℤ) × ℤ} (hZ : Z ∈ S) (hv : vis Z) {c : ℤ × (Fin 2 → ℤ)}
    (hc : c ∈ codes Z) : c ∈ isoKernelCodes S vis codes := by
  classical
  unfold isoKernelCodes
  rw [dif_pos hS]
  exact Finset.mem_biUnion.mpr ⟨Z, Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hZ, hv⟩, hc⟩

/-- Total table size over a finite family of groups. -/
theorem sum_isoKernelCodes_card_le {ι : Type*} (I : Finset ι) {S : Set ((Fin 3 → ℤ) × ℤ)}
    (hS : S.Finite) (vis : ι → (Fin 3 → ℤ) × ℤ → Prop)
    (codes : ι → (Fin 3 → ℤ) × ℤ → Finset (ℤ × (Fin 2 → ℤ)))
    (hcodes : ∀ i Z, (codes i Z).card ≤ 4) {L : ℝ}
    (hL : ∀ Z ∈ S, ∀ F ⊆ I, (∀ i ∈ F, vis i Z) → (F.card : ℝ) ≤ L) :
    (∑ i ∈ I, ((isoKernelCodes S (vis i) (codes i)).card : ℝ)) ≤
      4 * L * (hS.toFinset.card : ℝ) := by
  classical
  have hstep : ∀ i ∈ I, ((isoKernelCodes S (vis i) (codes i)).card : ℝ) ≤
      4 * ((hS.toFinset.filter (vis i)).card : ℝ) := by
    intro i _
    unfold isoKernelCodes
    rw [dif_pos hS]
    have h := Finset.card_biUnion_le (s := hS.toFinset.filter (vis i)) (t := codes i)
    have h' : ∑ Z ∈ hS.toFinset.filter (vis i), (codes i Z).card ≤
        ∑ _Z ∈ hS.toFinset.filter (vis i), 4 := Finset.sum_le_sum (fun Z _ => hcodes i Z)
    simp only [Finset.sum_const, smul_eq_mul] at h'
    have h'' := h.trans h'
    have : ((((hS.toFinset.filter (vis i)).biUnion (codes i)).card : ℕ) : ℝ) ≤
        (((hS.toFinset.filter (vis i)).card * 4 : ℕ) : ℝ) := by exact_mod_cast h''
    push_cast at this
    linarith
  have hswap : (∑ i ∈ I, ((hS.toFinset.filter (vis i)).card : ℝ)) =
      ∑ Z ∈ hS.toFinset, ((I.filter (fun i => vis i Z)).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    rw [Finset.sum_comm]
  calc
    (∑ i ∈ I, ((isoKernelCodes S (vis i) (codes i)).card : ℝ)) ≤
        ∑ i ∈ I, 4 * ((hS.toFinset.filter (vis i)).card : ℝ) := Finset.sum_le_sum hstep
    _ = 4 * ∑ Z ∈ hS.toFinset, ((I.filter (fun i => vis i Z)).card : ℝ) := by
      rw [← Finset.mul_sum, hswap]
    _ ≤ 4 * ∑ _Z ∈ hS.toFinset, L := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro Z hZ
      exact hL Z (hS.mem_toFinset.mp hZ) _ (Finset.filter_subset _ _)
        (fun i hi => (Finset.mem_filter.mp hi).2)
    _ = 4 * L * (hS.toFinset.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

end

end Submission.Obl.k4_horizon_chart_assembly
