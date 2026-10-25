-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordWidth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (PathData)

noncomputable section

/-- The actual path's size and determinant bounds resolve every
original-velocity strip. The scalar budget is independent of the root
level, format exponents and the number of original packets. -/
theorem original_record_strip_width
    {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ×(Fin 6 → ℝ))} {E : Fin W → Set ((ℕ×(Fin 6 → ℝ))×ℝ)}
    {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ N)
    (root : Fin p.C) {width radius : ℝ} (hw : 0 ≤ width)
    (hstrip : width*p.κ*N^(2*δ₀*L) ≤ radius) :
    width*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q root j l|) ≤
      radius*((2:ℝ)^p.T (p.lev root)*|(p.Q root).det|) := by
  rcases hp.2.2.2.2.2.2.2 root with
    ⟨hlev,_,_,_,_,hsize,_,_,_,_,_,_,_,_,_,hdetlow,_⟩
  obtain ⟨_,_,_,_,hnw,_⟩ := hp.2.2.2.2.1 (p.lev root) hlev
  simp only [zero_mul,sub_zero] at hnw
  have hnwle : p.nw (p.lev root) ≤ δ₀*L := (le_abs_self _).trans hnw
  have hraw : N^(-(2*δ₀*L)) ≤ |(p.Q root).det| * (4:ℝ)^p.T (p.lev root) :=
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans hdetlow
  have hpow : (4:ℝ)^p.T (p.lev root)=((2:ℝ)^p.T (p.lev root))^2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,←pow_mul,←pow_mul,Nat.mul_comm]
  rw [hpow] at hraw
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hκ : 0 ≤ p.κ := zero_le_one.trans hp.1
  have hr : 0 ≤ radius := (by positivity : 0 ≤ width*p.κ*N^(2*δ₀*L)).trans hstrip
  have hcancel : N^(2*δ₀*L)*N^(-(2*δ₀*L))=1 := by
    rw [←Real.rpow_add hNp,add_neg_cancel,Real.rpow_zero]
  have hwκ : width*p.κ ≤ radius*(|(p.Q root).det| * ((2:ℝ)^p.T (p.lev root))^2) := by
    calc
      width*p.κ = width*p.κ*(N^(2*δ₀*L)*N^(-(2*δ₀*L))) := by rw [hcancel,mul_one]
      _ ≤ radius*N^(-(2*δ₀*L)) := by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right hstrip (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hraw hr
  calc
    _ ≤ width*(p.κ/(2:ℝ)^p.T (p.lev root)) := mul_le_mul_of_nonneg_left hsize hw
    _ = (width*p.κ)/(2:ℝ)^p.T (p.lev root) := by ring
    _ ≤ (radius*(|(p.Q root).det| * ((2:ℝ)^p.T (p.lev root))^2))/
        (2:ℝ)^p.T (p.lev root) := by gcongr
    _ = _ := by field_simp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
