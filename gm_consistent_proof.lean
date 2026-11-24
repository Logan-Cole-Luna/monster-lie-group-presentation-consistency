import Mathlib
set_option autoImplicit false

namespace GM

structure EIdx (c : ℕ → ℕ) where
  l : ℕ
  j : ℕ
  k : ℕ
  hk1 : 1 ≤ k
  hkc : k ≤ c j
  hl : l < j

def EIdx.refl {c : ℕ → ℕ} (e : EIdx c) : EIdx c where
  l := e.j - 1 - e.l
  j := e.j
  k := e.k
  hk1 := e.hk1
  hkc := e.hkc
  hl := by have := e.hl; omega

inductive Gen (c : ℕ → ℕ) where
  | H1 : ℂˣ → Gen c
  | H2 : ℂˣ → Gen c
  | Xm : ℂ → Gen c
  | Ym : ℂ → Gen c
  | X : EIdx c → ℂ → Gen c
  | Y : EIdx c → ℂ → Gen c

/-- c_{ℓ j} = (-1)^{ℓ+1} binom(j-1, ℓ) (ℓ+1)(j-ℓ) -/
def cst (l j : ℕ) : ℂ :=
  (-1 : ℂ) ^ (l + 1) * (Nat.choose (j - 1) l : ℂ) * ((l : ℂ) + 1) * ((j : ℂ) - l)

section
variable {c : ℕ → ℕ}

abbrev h1 (s : ℂˣ) : FreeGroup (Gen c) := FreeGroup.of (Gen.H1 s)
abbrev h2 (s : ℂˣ) : FreeGroup (Gen c) := FreeGroup.of (Gen.H2 s)
abbrev xm (u : ℂ) : FreeGroup (Gen c) := FreeGroup.of (Gen.Xm u)
abbrev ym (u : ℂ) : FreeGroup (Gen c) := FreeGroup.of (Gen.Ym u)
abbrev x (e : EIdx c) (u : ℂ) : FreeGroup (Gen c) := FreeGroup.of (Gen.X e u)
abbrev y (e : EIdx c) (u : ℂ) : FreeGroup (Gen c) := FreeGroup.of (Gen.Y e u)

/-- (Re:0) w̃_{-1}(s) = X_{-1}(s) Y_{-1}(-s⁻¹) X_{-1}(s) -/
abbrev wt (s : ℂˣ) : FreeGroup (Gen c) :=
  xm (s : ℂ) * ym (-((s⁻¹ : ℂˣ) : ℂ)) * xm (s : ℂ)

/-- w̃_{-1} = w̃_{-1}(1) -/
abbrev w : FreeGroup (Gen c) := wt 1

/-- commutator -/
abbrev comm (a b : FreeGroup (Gen c)) : FreeGroup (Gen c) := a * b * a⁻¹ * b⁻¹

end

/-- The relators; a relation `a = b` is encoded as the relator `a * b⁻¹`. -/
inductive Rel (c : ℕ → ℕ) : FreeGroup (Gen c) → Prop
  | H1H1 (s t : ℂˣ) : Rel c (h1 s * h1 t * (h1 (s * t))⁻¹)
  | H2H2 (s t : ℂˣ) : Rel c (h2 s * h2 t * (h2 (s * t))⁻¹)
  | H1H2 (s t : ℂˣ) : Rel c (h1 s * h2 t * (h2 t * h1 s)⁻¹)
  | XX (u v : ℂ) : Rel c (xm u * xm v * (xm (u + v))⁻¹)
  | YY (u v : ℂ) : Rel c (ym u * ym v * (ym (u + v))⁻¹)
  | XY (s t : ℂˣ) : Rel c
      (ym (-(t : ℂ)) * xm (s : ℂ) * ym (t : ℂ) *
        (xm (-((t⁻¹ : ℂˣ) : ℂ)) * ym (-(t : ℂ) ^ 2 * s) * xm ((t⁻¹ : ℂˣ) : ℂ))⁻¹)
  | wwH (s : ℂˣ) : Rel c (wt s * w * (h1 (-s) * h2 (-s⁻¹))⁻¹)
  | wX (u : ℂ) : Rel c (w * xm u * w⁻¹ * (ym (-u))⁻¹)
  | wY (u : ℂ) : Rel c (w * ym u * w⁻¹ * (xm (-u))⁻¹)
  | wH1 (s : ℂˣ) : Rel c (w * h1 s * w⁻¹ * (h2 s)⁻¹)
  | wH2 (s : ℂˣ) : Rel c (w * h2 s * w⁻¹ * (h1 s)⁻¹)
  | H1X (s : ℂˣ) (u : ℂ) : Rel c (h1 s * xm u * (h1 s)⁻¹ * (xm ((s : ℂ) * u))⁻¹)
  | H2X (s : ℂˣ) (u : ℂ) : Rel c (h2 s * xm u * (h2 s)⁻¹ * (xm (((s⁻¹ : ℂˣ) : ℂ) * u))⁻¹)
  | H1Y (s : ℂˣ) (u : ℂ) : Rel c (h1 s * ym u * (h1 s)⁻¹ * (ym (((s⁻¹ : ℂˣ) : ℂ) * u))⁻¹)
  | H2Y (s : ℂˣ) (u : ℂ) : Rel c (h2 s * ym u * (h2 s)⁻¹ * (ym ((s : ℂ) * u))⁻¹)
  | ImXX (e : EIdx c) (u v : ℂ) : Rel c (x e u * x e v * (x e (u + v))⁻¹)
  | ImYY (e : EIdx c) (u v : ℂ) : Rel c (y e u * y e v * (y e (u + v))⁻¹)
  | ImXY (e : EIdx c) (s t : ℂˣ) : Rel c
      (y e (-(t : ℂ)) * x e (s : ℂ) * y e (t : ℂ) *
        (x e (-((t⁻¹ : ℂˣ) : ℂ) / cst e.l e.j) * y e (-(cst e.l e.j) * (t : ℂ) ^ 2 * s) *
          x e (((t⁻¹ : ℂˣ) : ℂ) / cst e.l e.j))⁻¹)
  | ImH1X (e : EIdx c) (s : ℂˣ) (u : ℂ) :
      Rel c (h1 s * x e u * (h1 s)⁻¹ * (x e ((s : ℂ) ^ (e.l + 1) * u))⁻¹)
  | ImH2X (e : EIdx c) (s : ℂˣ) (u : ℂ) :
      Rel c (h2 s * x e u * (h2 s)⁻¹ * (x e ((s : ℂ) ^ (e.j - e.l) * u))⁻¹)
  | ImH1Y (e : EIdx c) (s : ℂˣ) (u : ℂ) :
      Rel c (h1 s * y e u * (h1 s)⁻¹ * (y e (((s⁻¹ : ℂˣ) : ℂ) ^ (e.l + 1) * u))⁻¹)
  | ImH2Y (e : EIdx c) (s : ℂˣ) (u : ℂ) :
      Rel c (h2 s * y e u * (h2 s)⁻¹ * (y e (((s⁻¹ : ℂˣ) : ℂ) ^ (e.j - e.l) * u))⁻¹)
  | U1a (e : EIdx c) (he : e.l = e.j - 1) (u v : ℂ) : Rel c (comm (xm u) (x e v))
  | U1b (e : EIdx c) (he : e.l = e.j - 1) (u v : ℂ) : Rel c (comm (ym u) (y e v))
  | U1c (e : EIdx c) (he : e.l = 0) (u v : ℂ) : Rel c (comm (ym u) (x e v))
  | U1d (e : EIdx c) (he : e.l = 0) (u v : ℂ) : Rel c (comm (xm u) (y e v))
  | U2 (e f : EIdx c) (hef : e.j ≠ f.j ∨ e.k ≠ f.k ∨ 1 < Int.natAbs ((e.l : ℤ) - f.l))
      (u v : ℂ) : Rel c (comm (x e u) (y f v))
  | U4a (e : EIdx c) (u : ℂ) :
      Rel c (w * x e u * w⁻¹ * (x e.refl ((-1 : ℂ) ^ e.l * u))⁻¹)
  | U4b (e : EIdx c) (u : ℂ) :
      Rel c (w * y e u * w⁻¹ * (y e.refl ((-1 : ℂ) ^ (e.j - e.l - 1) * u))⁻¹)
  | U5a (s : ℂˣ) : Rel c
      (ym (s : ℂ) * (xm ((s⁻¹ : ℂˣ) : ℂ) * h1 (-s⁻¹) * h2 (-s) * w * xm ((s⁻¹ : ℂˣ) : ℂ))⁻¹)

/-- The group G_𝔪. -/
abbrev Gm (c : ℕ → ℕ) : Type := PresentedGroup {r : FreeGroup (Gen c) | Rel c r}

end GM

open GM

set_option maxHeartbeats 2000000 in
theorem setting_real_part_nontrivial (c : ℕ → ℕ) :
    (∀ u : ℂ, u ≠ 0 → (PresentedGroup.of (Gen.Xm u) : Gm c) ≠ 1) ∧
    (∀ u : ℂ, u ≠ 0 → (PresentedGroup.of (Gen.Ym u) : Gm c) ≠ 1) ∧
    (∀ s : ℂˣ, s ≠ 1 → (PresentedGroup.of (Gen.H1 s) : Gm c) ≠ 1) ∧
    (∀ s : ℂˣ, s ≠ 1 → (PresentedGroup.of (Gen.H2 s) : Gm c) ≠ 1) := by
  let gx : ℂ → GL (Fin 2) ℂ := fun u =>
    ⟨!![1, u; 0, 1], !![1, -u; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  let gy : ℂ → GL (Fin 2) ℂ := fun u =>
    ⟨!![1, 0; u, 1], !![1, 0; -u, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  let g1 : ℂˣ → GL (Fin 2) ℂ := fun s =>
    ⟨!![(s : ℂ), 0; 0, 1], !![((s⁻¹ : ℂˣ) : ℂ), 0; 0, 1], by simp [Matrix.one_fin_two],
      by simp [Matrix.one_fin_two]⟩
  let g2 : ℂˣ → GL (Fin 2) ℂ := fun s =>
    ⟨!![1, 0; 0, (s : ℂ)], !![1, 0; 0, ((s⁻¹ : ℂˣ) : ℂ)], by simp [Matrix.one_fin_two],
      by simp [Matrix.one_fin_two]⟩
  let f : Gen c → GL (Fin 2) ℂ := fun g =>
    match g with
    | .H1 s => g1 s
    | .H2 s => g2 s
    | .Xm u => gx u
    | .Ym u => gy u
    | .X _ _ => 1
    | .Y _ _ => 1
  have hrel : ∀ r ∈ {r : FreeGroup (Gen c) | Rel c r}, FreeGroup.lift f r = 1 := by
    intro r hr
    cases hr <;> simp only [map_mul, map_inv, FreeGroup.lift_apply_of, f, mul_one,
      inv_one, mul_inv_cancel, mul_inv_rev] <;> rw [Units.ext_iff]
    all_goals try simp only [Units.val_mul, Units.inv_mk, Units.val_one, gx, gy, g1, g2]
    all_goals try simp only [Matrix.mul_fin_two]
    all_goals try (ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring)
  have key : ∀ g : Gen c, (PresentedGroup.of g : Gm c) = 1 → f g = 1 := by
    intro g hg
    have := congrArg (PresentedGroup.toGroup hrel) hg
    rwa [PresentedGroup.toGroup.of, map_one] at this
  refine ⟨fun u hu h => ?_, fun u hu h => ?_, fun s hs h => ?_, fun s hs h => ?_⟩
  · have := congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) (key _ h)
    simp [f, gx] at this
    exact hu this
  · have := congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) (key _ h)
    simp [f, gy] at this
    exact hu this
  · have := congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) (key _ h)
    simp [f, g1] at this
    exact hs this
  · have := congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) (key _ h)
    simp [f, g2] at this
    exact hs this

open GM

set_option maxHeartbeats 2000000 in
theorem gm_gl2_rel_aux (c : ℕ → ℕ) (f0 : Gen c → GL (Fin 2) ℂ)
    (hH1 : ∀ s : ℂˣ, (f0 (Gen.H1 s) : Matrix (Fin 2) (Fin 2) ℂ) = !![(s : ℂ), 0; 0, 1])
    (hH2 : ∀ s : ℂˣ, (f0 (Gen.H2 s) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, (s : ℂ)])
    (hXm : ∀ u : ℂ, (f0 (Gen.Xm u) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, u; 0, 1])
    (hYm : ∀ u : ℂ, (f0 (Gen.Ym u) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; u, 1])
    (hX : ∀ (e : EIdx c) (u : ℂ), f0 (Gen.X e u) = 1)
    (hY : ∀ (e : EIdx c) (u : ℂ), f0 (Gen.Y e u) = 1) :
    ∀ r, Rel c r → FreeGroup.lift f0 r = 1 := by
  let gx : ℂ → GL (Fin 2) ℂ := fun u =>
    ⟨!![1, u; 0, 1], !![1, -u; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  let gy : ℂ → GL (Fin 2) ℂ := fun u =>
    ⟨!![1, 0; u, 1], !![1, 0; -u, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  let g1 : ℂˣ → GL (Fin 2) ℂ := fun s =>
    ⟨!![(s : ℂ), 0; 0, 1], !![((s⁻¹ : ℂˣ) : ℂ), 0; 0, 1], by simp [Matrix.one_fin_two],
      by simp [Matrix.one_fin_two]⟩
  let g2 : ℂˣ → GL (Fin 2) ℂ := fun s =>
    ⟨!![1, 0; 0, (s : ℂ)], !![1, 0; 0, ((s⁻¹ : ℂˣ) : ℂ)], by simp [Matrix.one_fin_two],
      by simp [Matrix.one_fin_two]⟩
  let f : Gen c → GL (Fin 2) ℂ := fun g =>
    match g with
    | .H1 s => g1 s
    | .H2 s => g2 s
    | .Xm u => gx u
    | .Ym u => gy u
    | .X _ _ => 1
    | .Y _ _ => 1
  have hf : f0 = f := by
    funext g
    cases g with
    | H1 s => exact Units.ext (hH1 s)
    | H2 s => exact Units.ext (hH2 s)
    | Xm u => exact Units.ext (hXm u)
    | Ym u => exact Units.ext (hYm u)
    | X e u => exact hX e u
    | Y e u => exact hY e u
  rw [hf]
  intro r hr
  cases hr <;> simp only [map_mul, map_inv, FreeGroup.lift_apply_of, f, mul_one,
    inv_one, mul_inv_cancel, mul_inv_rev] <;> rw [Units.ext_iff]
  all_goals try simp only [Units.val_mul, Units.inv_mk, Units.val_one, gx, gy, g1, g2]
  all_goals try simp only [Matrix.mul_fin_two]
  all_goals try (ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring)

theorem gm_gl2_rel (c : ℕ → ℕ) (f0 : Gen c → GL (Fin 2) ℂ)
    (hH1 : ∀ s : ℂˣ, (f0 (Gen.H1 s) : Matrix (Fin 2) (Fin 2) ℂ) = !![(s : ℂ), 0; 0, 1])
    (hH2 : ∀ s : ℂˣ, (f0 (Gen.H2 s) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, (s : ℂ)])
    (hXm : ∀ u : ℂ, (f0 (Gen.Xm u) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, u; 0, 1])
    (hYm : ∀ u : ℂ, (f0 (Gen.Ym u) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; u, 1])
    (hX : ∀ (e : EIdx c) (u : ℂ), f0 (Gen.X e u) = 1)
    (hY : ∀ (e : EIdx c) (u : ℂ), f0 (Gen.Y e u) = 1) :
    ∀ r, Rel c r → FreeGroup.lift f0 r = 1 := by
  exact gm_gl2_rel_aux c f0 hH1 hH2 hXm hYm hX hY

set_option maxHeartbeats 400000 in

theorem gm_refl_refl {c : ℕ → ℕ} (e : EIdx c) : e.refl.refl = e := by
  obtain ⟨l, j, k, hk1, hkc, hl⟩ := e
  simp only [EIdx.refl, EIdx.mk.injEq]
  refine ⟨by omega, trivial, trivial⟩

set_option maxHeartbeats 400000 in

theorem gm_weyl_matrix (g1 g2 : GL (Fin 2) ℂ)
    (h1 : (g1 : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; 0, 1])
    (h2 : (g2 : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; -1, 1]) :
    ((g1 * g2 * g1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := by
  calc
    ((g1 * g2 * g1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = ((g1 : GL (Fin 2) ℂ) * (g2 : GL (Fin 2) ℂ) * (g1 : GL (Fin 2) ℂ) : GL (Fin 2) ℂ) := by
      simp
    _ = ((g1 : Matrix (Fin 2) (Fin 2) ℂ) * (g2 : Matrix (Fin 2) (Fin 2) ℂ) * (g1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
      simp
    _ = (!![1, 1; 0, 1] * !![1, 0; -1, 1] * !![1, 1; 0, 1]) := by
      rw [h1, h2]
    _ = (!![1, 1; 0, 1] * !![1, 0; -1, 1] * !![1, 1; 0, 1]) := rfl
    _ = !![0, 1; -1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

set_option maxHeartbeats 400000 in

theorem gm_aeval_subst_mul (g h : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
        (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
        (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
      (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
      (MvPolynomial.aeval (![(h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
        (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
      (h : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
        (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
      (h : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
        f) =
    MvPolynomial.aeval (![((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 •
        MvPolynomial.X 0 + ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 •
        MvPolynomial.X 1,
      ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
        ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
      ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
        Fin 3 → MvPolynomial (Fin 3) ℂ) f := by
  let σg : Fin 3 → MvPolynomial (Fin 3) ℂ := ![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
    (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
    (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
    (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
    (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2]
  let τh : Fin 3 → MvPolynomial (Fin 3) ℂ := ![(h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
    (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
    (h : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
    (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
    (h : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2]
  let σgh : Fin 3 → MvPolynomial (Fin 3) ℂ := ![((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 •
    MvPolynomial.X 0 + ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 •
    MvPolynomial.X 1,
    ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
    ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
    ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2]
  have hcomp : (MvPolynomial.aeval σg).comp (MvPolynomial.aeval τh) = MvPolynomial.aeval σgh := by
    calc
      (MvPolynomial.aeval σg).comp (MvPolynomial.aeval τh) = MvPolynomial.aeval (fun i => (MvPolynomial.aeval σg) (τh i)) := by
        rw [MvPolynomial.comp_aeval]
      _ = MvPolynomial.aeval (MvPolynomial.aeval σg ∘ τh) := rfl
      _ = MvPolynomial.aeval σgh := by
        congr 1
        funext i
        fin_cases i <;> simp [σg, τh, σgh, Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Units.val_mul, smul_add, add_smul, smul_smul, mul_comm,
          add_left_comm, add_assoc]
  calc
    MvPolynomial.aeval σg (MvPolynomial.aeval τh f) = ((MvPolynomial.aeval σg).comp (MvPolynomial.aeval τh)) f := by
      simp
    _ = MvPolynomial.aeval σgh f := by rw [hcomp]
    _ = MvPolynomial.aeval (![((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 •
        MvPolynomial.X 0 + ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 •
        MvPolynomial.X 1,
      ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
        ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
      ((g * h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) f := by
      simp [σgh]

set_option maxHeartbeats 400000 in

theorem gm_aeval_subst_one (f : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.aeval (![((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
        ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
      ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
        ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
      ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
        Fin 3 → MvPolynomial (Fin 3) ℂ) f = f := by
  have h : (![((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
        ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
      ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
        ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
      ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
        Fin 3 → MvPolynomial (Fin 3) ℂ) = MvPolynomial.X := by
    ext i
    fin_cases i <;> simp
  rw [h]
  exact MvPolynomial.aeval_X_left_apply f

set_option maxHeartbeats 400000 in

theorem gm_L_inv (p q : Fin 3 →₀ ℕ) (hpq : p ≠ q) (u v : ℂ) (huv : u + v = 0) :
    (LinearMap.id + u • (MvPolynomial.lcoeff ℂ q).smulRight (MvPolynomial.monomial p (1 : ℂ))) ∘ₗ
      (LinearMap.id + v • (MvPolynomial.lcoeff ℂ q).smulRight (MvPolynomial.monomial p (1 : ℂ)))
      = LinearMap.id := by

  set N : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] MvPolynomial (Fin 3) ℂ :=
    (MvPolynomial.lcoeff ℂ q).smulRight (MvPolynomial.monomial p (1 : ℂ)) with hN
  apply LinearMap.ext
  intro f

  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply, hN, LinearMap.smulRight_apply]




  set a := (MvPolynomial.lcoeff ℂ q) f with ha

  have hinner : (MvPolynomial.lcoeff ℂ q) (f + v • (a • MvPolynomial.monomial p (1 : ℂ))) = a := by
    rw [map_add, map_smul, ha]

    rw [map_smul]

    simp only [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial]

    simp [hpq]

  rw [hinner]


  simp only [smul_smul]


  have hsum : (v * a) • MvPolynomial.monomial p (1 : ℂ) + (u * a) • MvPolynomial.monomial p (1 : ℂ) = 0 := by
    calc
      (v * a) • MvPolynomial.monomial p (1 : ℂ) + (u * a) • MvPolynomial.monomial p (1 : ℂ)
          = ((v * a) + (u * a)) • MvPolynomial.monomial p (1 : ℂ) := by rw [add_smul]
      _ = ((v + u) * a) • MvPolynomial.monomial p (1 : ℂ) := by ring
      _ = ((u + v) * a) • MvPolynomial.monomial p (1 : ℂ) := by rw [add_comm]
      _ = (0 * a) • MvPolynomial.monomial p (1 : ℂ) := by rw [huv]
      _ = 0 • MvPolynomial.monomial p (1 : ℂ) := by simp
      _ = 0 := by simp

  calc
    f + (v * a) • MvPolynomial.monomial p (1 : ℂ) + (u * a) • MvPolynomial.monomial p (1 : ℂ)
        = f + ((v * a) • MvPolynomial.monomial p (1 : ℂ) + (u * a) • MvPolynomial.monomial p (1 : ℂ)) := by abel
    _ = f + 0 := by rw [hsum]
    _ = f := by simp

theorem gm_tau_add (τ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) → ℂ →
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hτ : ∀ p q : Fin 3 →₀ ℕ, p ≠ q → ∀ (u : ℂ) (v : MvPolynomial (Fin 3) ℂ),
      τ p q u v = v + (u * MvPolynomial.coeff q v) • MvPolynomial.monomial p (1 : ℂ))
    (p q : Fin 3 →₀ ℕ) (hpq : p ≠ q) (u v : ℂ) :
    τ p q u * τ p q v = τ p q (u + v) := by
  apply LinearEquiv.ext
  intro w
  calc
    (τ p q u * τ p q v) w = τ p q u (τ p q v w) := by
      rfl
    _ = τ p q u (w + (v * MvPolynomial.coeff q w) • MvPolynomial.monomial p (1 : ℂ)) := by
      rw [hτ p q hpq v w]
    _ = (w + (v * MvPolynomial.coeff q w) • MvPolynomial.monomial p (1 : ℂ)) +
        (u * MvPolynomial.coeff q (w + (v * MvPolynomial.coeff q w) • MvPolynomial.monomial p (1 : ℂ))) •
        MvPolynomial.monomial p (1 : ℂ) := by
      rw [hτ p q hpq u (w + (v * MvPolynomial.coeff q w) • MvPolynomial.monomial p (1 : ℂ))]
    _ = w + (v * MvPolynomial.coeff q w) • MvPolynomial.monomial p (1 : ℂ) +
        (u * MvPolynomial.coeff q w) • MvPolynomial.monomial p (1 : ℂ) := by
      have coeff_q : MvPolynomial.coeff q (w + (v * MvPolynomial.coeff q w) • MvPolynomial.monomial p (1 : ℂ)) =
          MvPolynomial.coeff q w := by
        rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul]
        simp [hpq]
      rw [coeff_q]
    _ = w + ((v + u) * MvPolynomial.coeff q w) • MvPolynomial.monomial p (1 : ℂ) := by
      simp [add_smul, add_mul, add_assoc]
    _ = w + ((u + v) * MvPolynomial.coeff q w) • MvPolynomial.monomial p (1 : ℂ) := by
      ring
    _ = τ p q (u + v) w := by
      rw [hτ p q hpq (u + v) w]

theorem gm_tau_sl2 (τ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) → ℂ →
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hτ : ∀ p q : Fin 3 →₀ ℕ, p ≠ q → ∀ (u : ℂ) (v : MvPolynomial (Fin 3) ℂ),
      τ p q u v = v + (u * MvPolynomial.coeff q v) • MvPolynomial.monomial p (1 : ℂ))
    (p q : Fin 3 →₀ ℕ) (hpq : p ≠ q) (a b κ : ℂ) (hab : a * b = κ) (hκ : κ ≠ 0)
    (s t : ℂˣ) :
    τ q p (b * -(t : ℂ)) * τ p q (a * (s : ℂ)) * τ q p (b * (t : ℂ)) =
      τ p q (a * (-((t⁻¹ : ℂˣ) : ℂ) / κ)) *
        τ q p (b * (-κ * (t : ℂ) ^ 2 * s)) *
        τ p q (a * (((t⁻¹ : ℂˣ) : ℂ) / κ)) := by
  subst hab
  have ha : a ≠ 0 := left_ne_zero_of_mul hκ
  have hb : b ≠ 0 := right_ne_zero_of_mul hκ
  have ht : (t : ℂ) ≠ 0 := t.ne_zero
  have hqp : q ≠ p := hpq.symm
  apply LinearEquiv.ext
  intro v
  simp only [LinearEquiv.mul_apply, hτ p q hpq, hτ q p hqp]
  ext m
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
    if_pos rfl, if_neg hpq, if_neg hqp, smul_eq_mul, Units.val_inv_eq_inv_val]
  by_cases h1 : p = m <;> by_cases h2 : q = m
  · exact absurd (h1.trans h2.symm) hpq
  · subst h1
    simp only [if_true, if_neg hpq, if_neg hqp, ite_true, mul_one, mul_zero, add_zero,
      zero_add, one_pow]
    field_simp; ring
  · subst h2
    simp only [if_true, if_neg hpq, if_neg hqp, ite_true, mul_one, mul_zero, add_zero,
      zero_add, one_pow]
    field_simp; ring
  · simp only [if_neg h1, if_neg h2]; ring

set_option maxHeartbeats 400000 in

theorem gm_tau_comm (τ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) → ℂ →
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hτ : ∀ p q : Fin 3 →₀ ℕ, p ≠ q → ∀ (u : ℂ) (v : MvPolynomial (Fin 3) ℂ),
      τ p q u v = v + (u * MvPolynomial.coeff q v) • MvPolynomial.monomial p (1 : ℂ))
    (p q p' q' : Fin 3 →₀ ℕ) (hpq : p ≠ q) (hpq' : p' ≠ q') (hp : p ≠ p') (hq : q ≠ q')
    (u v : ℂ) :
    τ p q u * τ q' p' v = τ q' p' v * τ p q u := by
  apply LinearEquiv.ext
  intro w
  simp only [LinearEquiv.mul_apply]
  rw [hτ p q hpq u (τ q' p' v w)]
  rw [hτ q' p' hpq'.symm v (τ p q u w)]

  rw [hτ q' p' hpq'.symm v w]
  rw [hτ p q hpq u w]

  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
  by_cases hq_eq : q' = q
  · exfalso; exact hq.symm hq_eq
  · by_cases hp_eq : p = p'
    · exfalso; exact hp hp_eq
    · simp [hq_eq, hp_eq]
      abel_nf

set_option maxHeartbeats 400000 in

theorem gm_tau_ne_one (τ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) → ℂ →
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hτ : ∀ p q : Fin 3 →₀ ℕ, p ≠ q → ∀ (u : ℂ) (v : MvPolynomial (Fin 3) ℂ),
      τ p q u v = v + (u * MvPolynomial.coeff q v) • MvPolynomial.monomial p (1 : ℂ))
    (p q : Fin 3 →₀ ℕ) (hpq : p ≠ q) (u : ℂ) (hu : u ≠ 0) : τ p q u ≠ 1 := by
  intro h
  have hv := congrArg (fun (f : MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ) => 
    f (MvPolynomial.monomial q (1 : ℂ))) h
  simp only [LinearEquiv.coe_one] at hv
  rw [hτ p q hpq u (MvPolynomial.monomial q (1 : ℂ))] at hv
  simp only [MvPolynomial.coeff_monomial, ↓reduceIte] at hv
  have hcoeff := congrArg (MvPolynomial.coeff p) hv
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
    smul_eq_mul, mul_one, id] at hcoeff
  simp [Ne.symm hpq, add_comm] at hcoeff
  simpa using hu hcoeff

set_option maxHeartbeats 400000 in

theorem gm_conj_tau (τ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) → ℂ →
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hτ : ∀ p q : Fin 3 →₀ ℕ, p ≠ q → ∀ (u : ℂ) (v : MvPolynomial (Fin 3) ℂ),
      τ p q u v = v + (u * MvPolynomial.coeff q v) • MvPolynomial.monomial p (1 : ℂ))
    (φ : MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ)
    (p q p' q' : Fin 3 →₀ ℕ) (hpq : p ≠ q) (hpq' : p' ≠ q') (μ ν : ℂ)
    (hp : φ (MvPolynomial.monomial p 1) = μ • MvPolynomial.monomial p' 1)
    (hq : ∀ v, MvPolynomial.coeff q (φ⁻¹ v) = ν * MvPolynomial.coeff q' v) (u : ℂ) :
    φ * τ p q u * φ⁻¹ = τ p' q' (μ * ν * u) := by
  apply LinearEquiv.ext
  intro v
  calc
    (φ * τ p q u * φ⁻¹) v = (φ * τ p q u) (φ⁻¹ v) := by
      rw [LinearEquiv.mul_apply]
    _ = φ ((τ p q u) (φ⁻¹ v)) := by
      rw [LinearEquiv.mul_apply]
    _ = φ (φ⁻¹ v + (u * MvPolynomial.coeff q (φ⁻¹ v)) • MvPolynomial.monomial p 1) := by
      rw [hτ p q hpq u (φ⁻¹ v)]
    _ = φ (φ⁻¹ v) + (u * MvPolynomial.coeff q (φ⁻¹ v)) • φ (MvPolynomial.monomial p 1) := by
      rw [map_add, map_smul]
    _ = v + (u * MvPolynomial.coeff q (φ⁻¹ v)) • φ (MvPolynomial.monomial p 1) := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      simp
    _ = v + (u * (ν * MvPolynomial.coeff q' v)) • (μ • MvPolynomial.monomial p' 1) := by
      rw [hq v, hp]
    _ = v + ((u * (ν * MvPolynomial.coeff q' v)) * μ) • MvPolynomial.monomial p' 1 := by
      rw [smul_smul]
    _ = v + (μ * ν * u * MvPolynomial.coeff q' v) • MvPolynomial.monomial p' 1 := by
      ring
    _ = τ p' q' (μ * ν * u) v := by
      rw [hτ p' q' hpq' (μ * ν * u) v]

open MvPolynomial in
open GM in
set_option maxHeartbeats 400000 in
theorem gm_rho_diag_monomial_aiprover_s0 (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (a b : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![a, 0; 0, b])
    (m : Fin 3 →₀ ℕ) :
    ρ g (MvPolynomial.monomial m 1) =
      (a ^ (m 0) * b ^ (m 1) * (a * b) ^ (m 2)) • MvPolynomial.monomial m 1 := by
  rw [hρ g, hg]
  have hdet : (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℂ).det = a * b := by
    simp [Matrix.det_fin_two_of]
  rw [hdet]
  rw [MvPolynomial.aeval_monomial]
  simp
  rw [Fin.prod_univ_three]
  simp
  simp [smul_pow]
  rw [MvPolynomial.monomial_eq]
  simp only [smul_eq_C_mul]
  simp only [RingHom.map_mul, RingHom.map_pow, map_one]
  have hprod : (m.prod fun (n : Fin 3) (e : ℕ) => (X n ^ e : MvPolynomial (Fin 3) ℂ)) = (X 0 ^ (m 0)) * (X 1 ^ (m 1)) * (X 2 ^ (m 2)) := by
    rw [Finsupp.prod_fintype m (fun (n : Fin 3) (e : ℕ) => (X n ^ e : MvPolynomial (Fin 3) ℂ)) (fun i => by simp)]
    rw [Fin.prod_univ_three]
  rw [hprod]
  ring

theorem gm_rho_diag_monomial (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (a b : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![a, 0; 0, b])
    (m : Fin 3 →₀ ℕ) :
    ρ g (MvPolynomial.monomial m 1) =
      (a ^ (m 0) * b ^ (m 1) * (a * b) ^ (m 2)) • MvPolynomial.monomial m 1 := by
  first
    | exact gm_rho_diag_monomial_aiprover_s0
    | (intros; apply gm_rho_diag_monomial_aiprover_s0 <;> assumption)

set_option maxHeartbeats 400000 in

theorem gm_coeff_rho_diag (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (a b : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![a, 0; 0, b])
    (q : Fin 3 →₀ ℕ) (v : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.coeff q (ρ g v) =
      (a ^ (q 0) * b ^ (q 1) * (a * b) ^ (q 2)) * MvPolynomial.coeff q v := by
  let K := a ^ (q 0) * b ^ (q 1) * (a * b) ^ (q 2)
  refine MvPolynomial.induction_on' v ?_ ?_
  · intro m r

    have hmon : (MvPolynomial.monomial m r : MvPolynomial (Fin 3) ℂ) = r • MvPolynomial.monomial m 1 := by
      calc
        MvPolynomial.monomial m r = MvPolynomial.monomial m (r * 1) := by simp
        _ = MvPolynomial.monomial m (r • (1 : ℂ)) := by simp [smul_eq_mul]
        _ = r • MvPolynomial.monomial m 1 :=
          (MvPolynomial.smul_monomial (R := ℂ) (a := (1 : ℂ)) (s := m) (r := r)).symm
    rw [hmon]
    rw [map_smul]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]

    rw [gm_rho_diag_monomial ρ hρ g a b hg m]
    simp only [map_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
    by_cases hm : m = q
    · subst hm
      simp [K, mul_comm, mul_left_comm, mul_assoc]
    · simp [hm, K]
  · intro p q hp hq

    rw [map_add]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add]
    rw [hp, hq]
    ring

theorem gm_rho_W_monomial (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0])
    (m m' : Fin 3 →₀ ℕ) (h0 : m' 0 = m 1) (h1 : m' 1 = m 0) (h2 : m' 2 = m 2) :
    ρ g (MvPolynomial.monomial m 1) = ((-1 : ℂ) ^ (m 0)) • MvPolynomial.monomial m' 1 := by
  rw [hρ]


  have hsub : (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
      (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
      (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
      (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2]
      : Fin 3 → MvPolynomial (Fin 3) ℂ) = fun i =>
    match i with
    | 0 => (-1 : ℂ) • MvPolynomial.X 1
    | 1 => MvPolynomial.X 0
    | 2 => MvPolynomial.X 2 := by
    ext i
    fin_cases i <;> simp [hg, Matrix.det_fin_two_of]
  rw [hsub]

  have hm : MvPolynomial.monomial m (1 : ℂ) =
      MvPolynomial.X 0 ^ m 0 * MvPolynomial.X 1 ^ m 1 * MvPolynomial.X 2 ^ m 2 := by
    rw [MvPolynomial.monomial_eq]
    simp [Finsupp.prod_fintype, Fin.prod_univ_three]
  have hm' : MvPolynomial.monomial m' (1 : ℂ) =
      MvPolynomial.X 0 ^ m' 0 * MvPolynomial.X 1 ^ m' 1 * MvPolynomial.X 2 ^ m' 2 := by
    rw [MvPolynomial.monomial_eq]
    simp [Finsupp.prod_fintype, Fin.prod_univ_three]
  rw [hm, hm']

  simp only [map_mul, map_pow, MvPolynomial.aeval_X]

  rw [h0, h1, h2]

  simp [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_pow]
  ring

set_option maxHeartbeats 400000 in

theorem gm_coeff_rho_W_inv (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0])
    (q q' : Fin 3 →₀ ℕ) (h0 : q' 0 = q 1) (h1 : q' 1 = q 0) (h2 : q' 2 = q 2)
    (v : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.coeff q ((ρ g)⁻¹ v) = (-1 : ℂ) ^ (q 0) * MvPolynomial.coeff q' v := by

  set w := (ρ g)⁻¹ v with hw_def
  have hw_eq : ρ g w = v := by
    rw [hw_def]
    exact (ρ g).apply_symm_apply v


  rw [hw_def]

  have h_sq : ((-1 : ℂ) ^ (q 0)) * ((-1 : ℂ) ^ (q 0)) = 1 := by
    calc
      ((-1 : ℂ) ^ (q 0)) * ((-1 : ℂ) ^ (q 0)) = ((-1 : ℂ) * (-1 : ℂ)) ^ (q 0) := by
        rw [mul_pow]
      _ = (1 : ℂ) ^ (q 0) := by simp
      _ = 1 := by simp
  have hkey : ∀ (w : MvPolynomial (Fin 3) ℂ),
      MvPolynomial.coeff q' (ρ g w) = (-1 : ℂ) ^ (q 0) * MvPolynomial.coeff q w := by
    intro w
    refine MvPolynomial.induction_on' w ?_ ?_
    · 
      intro u a

      let m' : Fin 3 →₀ ℕ :=
        Finsupp.equivFunOnFinite.symm (fun i => u (Equiv.swap 0 1 i))
      have hm'0 : m' 0 = u 1 := by
        simp [m', Equiv.swap_apply_left]
      have hm'1 : m' 1 = u 0 := by
        simp [m', Equiv.swap_apply_right]
      have hm'2 : m' 2 = u 2 := by
        simp [m', Equiv.swap_apply_of_ne_of_ne]
      have h_rho_monom : ρ g (MvPolynomial.monomial u 1) =
          ((-1 : ℂ) ^ (u 0)) • MvPolynomial.monomial m' 1 :=
        gm_rho_W_monomial ρ hρ g hg u m' hm'0 hm'1 hm'2
      calc
        MvPolynomial.coeff q' (ρ g (MvPolynomial.monomial u a)) =
            MvPolynomial.coeff q' (ρ g (a • MvPolynomial.monomial u (1 : ℂ))) := by
          rw [show MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : ℂ) from by
            simpa using (MvPolynomial.smul_monomial (r := a) (s := u) (a := (1 : ℂ))).symm]
        _ = MvPolynomial.coeff q' (a • ρ g (MvPolynomial.monomial u (1 : ℂ))) := by
          rw [map_smul]
        _ = a * MvPolynomial.coeff q' (ρ g (MvPolynomial.monomial u (1 : ℂ))) := by
          simpa using MvPolynomial.coeff_smul (r := a) (p := ρ g (MvPolynomial.monomial u (1 : ℂ)))
            (q := q')
        _ = a * MvPolynomial.coeff q' (((-1 : ℂ) ^ (u 0)) • MvPolynomial.monomial m' (1 : ℂ)) := by
          rw [h_rho_monom]
        _ = a * (((-1 : ℂ) ^ (u 0)) * MvPolynomial.coeff q' (MvPolynomial.monomial m' (1 : ℂ))) := by
          simpa using MvPolynomial.coeff_smul (r := (-1 : ℂ) ^ (u 0))
            (p := MvPolynomial.monomial m' (1 : ℂ)) (q := q')
        _ = a * ((-1 : ℂ) ^ (u 0)) * MvPolynomial.coeff q' (MvPolynomial.monomial m' (1 : ℂ)) := by ring
        _ = a * ((-1 : ℂ) ^ (u 0)) * (if m' = q' then 1 else 0) := by
          simp [MvPolynomial.coeff_monomial]
        _ = (-1 : ℂ) ^ (q 0) * a * (if u = q then 1 else 0) := by
          by_cases hu : u = q
          · have hm'_eq_q' : m' = q' := by
              ext i
              fin_cases i
              · rw [hu] at hm'0
                calc
                  m' 0 = q 1 := hm'0
                  _ = q' 0 := h0.symm
              · rw [hu] at hm'1
                calc
                  m' 1 = q 0 := hm'1
                  _ = q' 1 := h1.symm
              · rw [hu] at hm'2
                calc
                  m' 2 = q 2 := hm'2
                  _ = q' 2 := h2.symm
            simp [hm'_eq_q', hu, mul_comm]
          · have hm'_ne_q' : m' ≠ q' := by
              intro h_eq
              apply hu
              apply Finsupp.ext
              intro i
              fin_cases i
              · calc
                  u 0 = m' 1 := (hm'1).symm
                  _ = q' 1 := by rw [h_eq]
                  _ = q 0 := h1
              · calc
                  u 1 = m' 0 := (hm'0).symm
                  _ = q' 0 := by rw [h_eq]
                  _ = q 1 := h0
              · calc
                  u 2 = m' 2 := (hm'2).symm
                  _ = q' 2 := by rw [h_eq]
                  _ = q 2 := h2
            simp [hu, hm'_ne_q']
        _ = (-1 : ℂ) ^ (q 0) * MvPolynomial.coeff q (MvPolynomial.monomial u a) := by
          simp [MvPolynomial.coeff_monomial]
    · 
      intro p q hp hq
      simp [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]
  have hkey_w := hkey w
  rw [hw_eq] at hkey_w


  calc
    MvPolynomial.coeff q w = 1 * MvPolynomial.coeff q w := by simp
    _ = (((-1 : ℂ) ^ (q 0)) * ((-1 : ℂ) ^ (q 0))) * MvPolynomial.coeff q w := by rw [h_sq]
    _ = (-1 : ℂ) ^ (q 0) * (((-1 : ℂ) ^ (q 0)) * MvPolynomial.coeff q w) := by ring
    _ = (-1 : ℂ) ^ (q 0) * MvPolynomial.coeff q' v := by rw [← hkey_w]

open MvPolynomial in
set_option maxHeartbeats 400000 in
theorem gm_rho_ux_monomial_aiprover_s0 (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (u : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![1, u; 0, 1])
    (m : Fin 3 →₀ ℕ) (hm : m 1 = 0) :
    ρ g (MvPolynomial.monomial m 1) = MvPolynomial.monomial m 1 := by
  rw [hρ g, hg]
  simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.det_fin_two_of]
  rw [bind₁_monomial]
  simp
  
  rw [monomial_eq]
  simp
  
  
  rw [← Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
    have hi' : m i = 0 := Finsupp.not_mem_support_iff.mp hi
    simp [hi'])]
  
  
  have hsupp : m.support ⊆ Finset.univ := Finset.subset_univ _
  rw [Finset.prod_subset hsupp (fun i _ hi => by
    have hi' : m i = 0 := Finsupp.not_mem_support_iff.mp hi
    simp [hi'])]
  rw [Finset.prod_subset hsupp (fun i _ hi => by
    have hi' : m i = 0 := Finsupp.not_mem_support_iff.mp hi
    simp [hi'])]
  
  simp [Fin.prod_univ_three]
  
  rw [hm]
  simp [pow_zero, mul_one]

theorem gm_rho_ux_monomial (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (u : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![1, u; 0, 1])
    (m : Fin 3 →₀ ℕ) (hm : m 1 = 0) :
    ρ g (MvPolynomial.monomial m 1) = MvPolynomial.monomial m 1 := by
  first
    | exact gm_rho_ux_monomial_aiprover_s0
    | (intros; apply gm_rho_ux_monomial_aiprover_s0 <;> assumption)

theorem gm_coeff_rho_ux_inv_kill (q : Fin 3 →₀ ℕ) (hq : q 0 = 0) (f : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.coeff q (MvPolynomial.aeval (![0, MvPolynomial.X 1, MvPolynomial.X 2] :
      Fin 3 → MvPolynomial (Fin 3) ℂ) f) = MvPolynomial.coeff q f := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by intro i; simp),
      Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    by_cases hm : m 0 = 0
    · have hm' : m = Finsupp.single 1 (m 1) + Finsupp.single 2 (m 2) := by
        ext i; fin_cases i <;> simp [hm]
      rw [hm, pow_zero, one_mul, MvPolynomial.algebraMap_eq, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial,
        mul_one, mul_one, ← hm']
    · rw [zero_pow hm, zero_mul, zero_mul, mul_zero, MvPolynomial.coeff_zero,
        MvPolynomial.coeff_monomial, if_neg]
      intro h; exact hm (h ▸ hq)
  | add p r hp hr => simp only [map_add, MvPolynomial.coeff_add, hp, hr]

theorem gm_coeff_rho_ux_inv_fix (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (u : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![1, u; 0, 1])
    (f : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.aeval (![0, MvPolynomial.X 1, MvPolynomial.X 2] :
      Fin 3 → MvPolynomial (Fin 3) ℂ) (ρ g f) =
    MvPolynomial.aeval (![0, MvPolynomial.X 1, MvPolynomial.X 2] :
      Fin 3 → MvPolynomial (Fin 3) ℂ) f := by
  rw [hρ, hg, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  fin_cases i <;> simp [Matrix.det_fin_two]

theorem gm_coeff_rho_ux_inv (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (u : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![1, u; 0, 1])
    (q : Fin 3 →₀ ℕ) (hq : q 0 = 0) (v : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.coeff q ((ρ g)⁻¹ v) = MvPolynomial.coeff q v := by
  have hw : ρ g ((ρ g)⁻¹ v) = v := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  conv_rhs => rw [← hw]
  rw [← gm_coeff_rho_ux_inv_kill q hq ((ρ g)⁻¹ v),
    ← gm_coeff_rho_ux_inv_kill q hq (ρ g ((ρ g)⁻¹ v)),
    gm_coeff_rho_ux_inv_fix ρ hρ g u hg]

set_option maxHeartbeats 400000 in

theorem gm_rho_uy_monomial (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (u : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; u, 1])
    (m : Fin 3 →₀ ℕ) (hm : m 0 = 0) :
    ρ g (MvPolynomial.monomial m 1) = MvPolynomial.monomial m 1 := by
  rw [hρ g]
  rw [hg]
  have hdet : (1 : ℂ) - (0 : ℂ) * u = 1 := by simp
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.det_fin_two_of, one_smul, zero_smul, zero_add, mul_one, hdet]
  rw [MvPolynomial.aeval_monomial]
  rw [map_one, one_mul]
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  rw [Finsupp.prod_fintype m (fun i k => (![MvPolynomial.X 0 + u • MvPolynomial.X 1, MvPolynomial.X 1, MvPolynomial.X 2] i) ^ k) (by simp)]
  rw [Finsupp.prod_fintype m (fun i k => MvPolynomial.X i ^ k) (by simp)]
  simp only [Fin.prod_univ_three]
  simp [hm, pow_zero]

theorem gm_coeff_rho_uy_inv_E (q : Fin 3 →₀ ℕ) (hq : q 1 = 0) (f : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.coeff q (MvPolynomial.aeval
      (![MvPolynomial.X 0, 0, MvPolynomial.X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) f) =
      MvPolynomial.coeff q f := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    by_cases hm : m 1 = 0
    · rw [hm, pow_zero, mul_one, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.monomial_mul, MvPolynomial.algebraMap_eq, MvPolynomial.C_mul_monomial,
        MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial, mul_one]
      have : Finsupp.single 0 (m 0) + Finsupp.single 2 (m 2) = m := by
        ext i; fin_cases i <;> simp [hm]
      rw [this, mul_one]
    · rw [zero_pow hm, mul_zero, zero_mul, mul_zero, MvPolynomial.coeff_zero,
        MvPolynomial.coeff_monomial, if_neg]
      intro h; apply hm; rw [h, hq]
  | add a b ha hb => rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, ha, hb]

theorem gm_coeff_rho_uy_inv (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (g : GL (Fin 2) ℂ) (u : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; u, 1])
    (q : Fin 3 →₀ ℕ) (hq : q 1 = 0) (v : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.coeff q ((ρ g)⁻¹ v) = MvPolynomial.coeff q v := by
  have hv : ρ g ((ρ g)⁻¹ v) = v := by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  have hE : ∀ f, MvPolynomial.aeval
      (![MvPolynomial.X 0, 0, MvPolynomial.X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) (ρ g f) =
      MvPolynomial.aeval
      (![MvPolynomial.X 0, 0, MvPolynomial.X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) f := by
    intro f
    rw [hρ, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext i; fin_cases i <;> simp [hg, Matrix.det_fin_two]
  rw [← gm_coeff_rho_uy_inv_E q hq ((ρ g)⁻¹ v), ← hE, hv, gm_coeff_rho_uy_inv_E q hq v]

set_option maxHeartbeats 400000 in

theorem gm_conj_diag (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (τ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) → ℂ →
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hτ : ∀ p q : Fin 3 →₀ ℕ, p ≠ q → ∀ (u : ℂ) (v : MvPolynomial (Fin 3) ℂ),
      τ p q u v = v + (u * MvPolynomial.coeff q v) • MvPolynomial.monomial p (1 : ℂ))
    (g : GL (Fin 2) ℂ) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![a, 0; 0, b])
    (p q : Fin 3 →₀ ℕ) (hpq : p ≠ q) (κ α : ℂ)
    (hw : a ^ (p 0 + p 2) * b ^ (p 1 + p 2) = κ * (a ^ (q 0 + q 2) * b ^ (q 1 + q 2)))
    (u : ℂ) :
    ρ g * τ p q (α * u) * (ρ g)⁻¹ = τ p q (α * (κ * u)) := by
  set Wp := a ^ (p 0) * b ^ (p 1) * (a * b) ^ (p 2) with hWp
  set Wq := a ^ (q 0) * b ^ (q 1) * (a * b) ^ (q 2) with hWq
  have hWq_ne_zero : Wq ≠ 0 := by
    rw [hWq]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact pow_ne_zero _ ha
    · exact pow_ne_zero _ hb
    · exact pow_ne_zero _ (mul_ne_zero ha hb)
  have hp : (ρ g) (MvPolynomial.monomial p 1) = Wp • MvPolynomial.monomial p 1 := by
    rw [hWp]
    exact gm_rho_diag_monomial ρ hρ g a b hg p
  have hq : ∀ v, MvPolynomial.coeff q ((ρ g)⁻¹ v) = (Wq⁻¹) * MvPolynomial.coeff q v := by
    intro v
    have h := gm_coeff_rho_diag ρ hρ g a b hg q ((ρ g)⁻¹ v)
    have h_apply : (ρ g) ((ρ g)⁻¹ v) = v := by
      have h_mul : (ρ g) * (ρ g)⁻¹ = (1 : MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ) := by
        simp
      calc
        (ρ g) ((ρ g)⁻¹ v) = ((ρ g) * (ρ g)⁻¹) v := rfl
        _ = ((1 : MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ)) v := by rw [h_mul]
        _ = v := by simp
    rw [h_apply] at h
    calc
      MvPolynomial.coeff q ((ρ g)⁻¹ v) = 1 * MvPolynomial.coeff q ((ρ g)⁻¹ v) := by simp
      _ = (Wq⁻¹ * Wq) * MvPolynomial.coeff q ((ρ g)⁻¹ v) := by rw [inv_mul_cancel₀ hWq_ne_zero]
      _ = Wq⁻¹ * (Wq * MvPolynomial.coeff q ((ρ g)⁻¹ v)) := by ring
      _ = Wq⁻¹ * MvPolynomial.coeff q v := by rw [← h]
  have hWp_eq : Wp = a ^ (p 0 + p 2) * b ^ (p 1 + p 2) := by
    rw [hWp]
    calc
      a ^ (p 0) * b ^ (p 1) * (a * b) ^ (p 2)
          = a ^ (p 0) * b ^ (p 1) * (a ^ (p 2) * b ^ (p 2)) := by rw [mul_pow]
      _ = (a ^ (p 0) * a ^ (p 2)) * (b ^ (p 1) * b ^ (p 2)) := by ring
      _ = a ^ (p 0 + p 2) * b ^ (p 1 + p 2) := by rw [pow_add, pow_add]
  have hWq_eq : Wq = a ^ (q 0 + q 2) * b ^ (q 1 + q 2) := by
    rw [hWq]
    calc
      a ^ (q 0) * b ^ (q 1) * (a * b) ^ (q 2)
          = a ^ (q 0) * b ^ (q 1) * (a ^ (q 2) * b ^ (q 2)) := by rw [mul_pow]
      _ = (a ^ (q 0) * a ^ (q 2)) * (b ^ (q 1) * b ^ (q 2)) := by ring
      _ = a ^ (q 0 + q 2) * b ^ (q 1 + q 2) := by rw [pow_add, pow_add]
  have h_mul : Wp * (Wq⁻¹) * (α * u) = α * (κ * u) := by
    have hWp_eq_kappa_Wq : Wp = κ * Wq := by
      rw [hWp_eq, hWq_eq]
      exact hw
    calc
      Wp * (Wq⁻¹) * (α * u) = (κ * Wq) * (Wq⁻¹) * (α * u) := by rw [hWp_eq_kappa_Wq]
      _ = κ * (Wq * Wq⁻¹) * (α * u) := by ring
      _ = κ * 1 * (α * u) := by rw [mul_inv_cancel₀ hWq_ne_zero]
      _ = κ * (α * u) := by simp
      _ = α * (κ * u) := by ring
  have h_conj := gm_conj_tau τ hτ (ρ g) p q p q hpq hpq Wp (Wq⁻¹) hp hq (α * u)
  rw [h_conj]
  rw [h_mul]

theorem gm_conj_W (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (τ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) → ℂ →
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hτ : ∀ p q : Fin 3 →₀ ℕ, p ≠ q → ∀ (u : ℂ) (v : MvPolynomial (Fin 3) ℂ),
      τ p q u v = v + (u * MvPolynomial.coeff q v) • MvPolynomial.monomial p (1 : ℂ))
    (g : GL (Fin 2) ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0])
    (p q p' q' : Fin 3 →₀ ℕ) (hpq : p ≠ q) (hpq' : p' ≠ q')
    (hp0 : p' 0 = p 1) (hp1 : p' 1 = p 0) (hp2 : p' 2 = p 2)
    (hq0 : q' 0 = q 1) (hq1 : q' 1 = q 0) (hq2 : q' 2 = q 2) (α α' σ : ℂ)
    (hs : (-1 : ℂ) ^ (p 0) * (-1 : ℂ) ^ (q 0) * α = α' * σ) (u : ℂ) :
    ρ g * τ p q (α * u) * (ρ g)⁻¹ = τ p' q' (α' * (σ * u)) := by
  have h := gm_conj_tau τ hτ (ρ g) p q p' q' hpq hpq' ((-1 : ℂ) ^ (p 0)) ((-1 : ℂ) ^ (q 0))
    (gm_rho_W_monomial ρ hρ g hg p p' hp0 hp1 hp2)
    (fun v => gm_coeff_rho_W_inv ρ hρ g hg q q' hq0 hq1 hq2 v)
    (α * u)

  rw [h]
  congr 1
  calc
    ((-1 : ℂ) ^ (p 0)) * ((-1 : ℂ) ^ (q 0)) * (α * u)
        = (((-1 : ℂ) ^ (p 0)) * ((-1 : ℂ) ^ (q 0)) * α) * u := by ring
    _ = (α' * σ) * u := by rw [hs]
    _ = α' * (σ * u) := by ring

set_option maxHeartbeats 400000 in

theorem gm_comm_ux (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (τ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) → ℂ →
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hτ : ∀ p q : Fin 3 →₀ ℕ, p ≠ q → ∀ (u : ℂ) (v : MvPolynomial (Fin 3) ℂ),
      τ p q u v = v + (u * MvPolynomial.coeff q v) • MvPolynomial.monomial p (1 : ℂ))
    (g : GL (Fin 2) ℂ) (t : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![1, t; 0, 1])
    (p q : Fin 3 →₀ ℕ) (hpq : p ≠ q) (hp : p 1 = 0) (hq : q 0 = 0) (u : ℂ) :
    ρ g * τ p q u = τ p q u * ρ g := by

  have hconj := gm_conj_tau τ hτ (ρ g) p q p q hpq hpq 1 1 ?hp ?hq u
  · 

    simp only [one_mul] at hconj



    calc
      ρ g * τ p q u = (ρ g * τ p q u) * 1 := by simp
      _ = (ρ g * τ p q u) * ((ρ g)⁻¹ * ρ g) := by simp
      _ = ((ρ g * τ p q u) * (ρ g)⁻¹) * ρ g := by group
      _ = τ p q u * ρ g := by rw [hconj]
  · 

    have h := gm_rho_ux_monomial ρ hρ g t hg p hp

    simpa [one_smul] using h
  · 
    intro v
    have h := gm_coeff_rho_ux_inv ρ hρ g t hg q hq v

    simpa [one_mul] using h

set_option maxHeartbeats 400000 in

theorem gm_comm_uy (ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hρ : ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
      MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
        (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) f)
    (τ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) → ℂ →
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ))
    (hτ : ∀ p q : Fin 3 →₀ ℕ, p ≠ q → ∀ (u : ℂ) (v : MvPolynomial (Fin 3) ℂ),
      τ p q u v = v + (u * MvPolynomial.coeff q v) • MvPolynomial.monomial p (1 : ℂ))
    (g : GL (Fin 2) ℂ) (t : ℂ) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; t, 1])
    (p q : Fin 3 →₀ ℕ) (hpq : p ≠ q) (hp : p 0 = 0) (hq : q 1 = 0) (u : ℂ) :
    ρ g * τ p q u = τ p q u * ρ g := by
  have h_monomial : ρ g (MvPolynomial.monomial p 1) = (1 : ℂ) • MvPolynomial.monomial p 1 := by
    rw [one_smul]
    exact gm_rho_uy_monomial ρ hρ g t hg p hp
  have h_coeff : ∀ (v : MvPolynomial (Fin 3) ℂ), MvPolynomial.coeff q ((ρ g)⁻¹ v) = (1 : ℂ) * MvPolynomial.coeff q v := by
    intro v
    rw [one_mul]
    exact gm_coeff_rho_uy_inv ρ hρ g t hg q hq v
  have h_conj : ρ g * τ p q u * (ρ g)⁻¹ = τ p q u := by
    have := gm_conj_tau τ hτ (ρ g) p q p q hpq hpq (1 : ℂ) (1 : ℂ) h_monomial h_coeff u
    simpa [one_mul] using this
  apply mul_inv_eq_iff_eq_mul.mp
  exact h_conj

set_option maxHeartbeats 400000 in

theorem gm_pow_inv_mul (x : ℂ) (hx : x ≠ 0) (a k : ℕ) : x ^ a = (x ^ k)⁻¹ * x ^ (a + k) := by
  rw [pow_add, mul_comm (x ^ a) (x ^ k), inv_mul_cancel_left₀ (pow_ne_zero k hx)]

theorem gm_cst_ne_zero (l j : ℕ) (h : l < j) : cst l j ≠ 0 := by
  simp only [cst]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · 
    apply pow_ne_zero
    simp
  · 
    have hle : l ≤ j - 1 := by omega
    have hpos : 0 < Nat.choose (j - 1) l := Nat.choose_pos hle
    exact Nat.cast_ne_zero.mpr hpos.ne'
  · 
    exact Nat.cast_add_one_ne_zero l
  · 
    apply sub_ne_zero.mpr
    intro h_eq
    have : (j : ℕ) = (l : ℕ) := Nat.cast_inj.mp h_eq
    exact h.ne' this

set_option maxHeartbeats 400000 in

theorem gm_pos_cst (l j : ℕ) (h : l < j) :
    (-1 : ℂ) ^ (l + 1) * -(cst l j * (-1 : ℂ) ^ (j - l - 1)) = cst (j - 1 - l) j := by

  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h

  have hsub1 : (l + d + 1 : ℕ) - l - 1 = d := by omega
  have hsub2 : (l + d + 1 : ℕ) - 1 - l = d := by omega
  rw [hsub1, hsub2]

  unfold cst

  have hsub3 : (l + d + 1 : ℕ) - 1 = l + d := by omega
  rw [hsub3]

  push_cast

  simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

  have hbinom : (Nat.choose (l + d) d : ℂ) = (Nat.choose (l + d) l : ℂ) := by
    norm_cast
    rw [Nat.choose_symm_add]
  rw [hbinom]

  simp [pow_succ]

  have hsign_l := neg_one_pow_eq_or ℂ l
  have hsign_d := neg_one_pow_eq_or ℂ d
  rcases hsign_l with (hl | hl)
  · rcases hsign_d with (hd | hd)
    · rw [hl, hd]; ring
    · rw [hl, hd]; ring
  · rcases hsign_d with (hd | hd)
    · rw [hl, hd]; ring
    · rw [hl, hd]; ring

set_option maxHeartbeats 400000 in

theorem gm_pos_signX (l a b : ℕ) (ha : a = 1) (hb : b = 0) :
    (-1 : ℂ) ^ a * (-1 : ℂ) ^ b * 1 = (-1 : ℂ) ^ (l + 1) * (-1 : ℂ) ^ l := by
  subst ha; subst hb
  simp
  have hsq : (-1 : ℂ) ^ l * (-1 : ℂ) ^ l = 1 := by
    calc
      (-1 : ℂ) ^ l * (-1 : ℂ) ^ l = ((-1 : ℂ) * (-1 : ℂ)) ^ l := by rw [mul_pow]
      _ = (1 : ℂ) ^ l := by norm_num
      _ = 1 := by simp
  calc
    (-1 : ℂ) = (-1 : ℂ) * 1 := by simp
    _ = (-1 : ℂ) * ((-1 : ℂ) ^ l * (-1 : ℂ) ^ l) := by rw [hsq]
    _ = (-1 : ℂ) ^ l * (-1 : ℂ) * (-1 : ℂ) ^ l := by ring
    _ = (-1 : ℂ) ^ (l + 1) * (-1 : ℂ) ^ l := by rw [pow_succ]

set_option maxHeartbeats 400000 in

theorem gm_pos_signY (l j a b : ℕ) (ha : a = 0) (hb : b = 1) (κ : ℂ) :
    (-1 : ℂ) ^ a * (-1 : ℂ) ^ b * κ = -(κ * (-1 : ℂ) ^ (j - l - 1)) * (-1 : ℂ) ^ (j - l - 1) := by
  subst ha
  subst hb
  have hsq : ((-1 : ℂ) ^ (j - l - 1)) ^ 2 = 1 := by
    calc
      ((-1 : ℂ) ^ (j - l - 1)) ^ 2 = (-1 : ℂ) ^ ((j - l - 1) * 2) := by rw [pow_mul]
      _ = (-1 : ℂ) ^ (2 * (j - l - 1)) := by rw [mul_comm]
      _ = ((-1 : ℂ) ^ 2) ^ (j - l - 1) := by rw [← pow_mul]
      _ = (1 : ℂ) ^ (j - l - 1) := by simp
      _ = 1 := by simp
  calc
    (-1 : ℂ) ^ 0 * (-1 : ℂ) ^ 1 * κ = (-1 : ℂ) * κ := by simp
    _ = -(κ * 1) := by ring
    _ = -(κ * ((-1 : ℂ) ^ (j - l - 1)) ^ 2) := by rw [hsq]
    _ = -(κ * (-1 : ℂ) ^ (j - l - 1)) * (-1 : ℂ) ^ (j - l - 1) := by ring

theorem gm_pos_signX' (l j a b : ℕ) (hlj : l < j) (h : j ≤ 2 * l) (ha : a = 0)
    (hb : b = 2 * l - j) :
    (-1 : ℂ) ^ a * (-1 : ℂ) ^ b * (-1 : ℂ) ^ (l + 1) = 1 * (-1 : ℂ) ^ (j - 1 - l) := by
  subst ha
  subst hb
  simp


  rw [← pow_add]

  have h_exp_eq : (2 * l - j) + (l + 1) = (j - 1 - l) + 2 * (2 * l - j + 1) := by
    omega
  rw [h_exp_eq]
  rw [pow_add]
  calc
    (-1 : ℂ) ^ (j - 1 - l) * (-1 : ℂ) ^ (2 * (2 * l - j + 1))
        = (-1 : ℂ) ^ (j - 1 - l) * (((-1 : ℂ) ^ 2) ^ (2 * l - j + 1)) := by rw [pow_mul]
    _ = (-1 : ℂ) ^ (j - 1 - l) * (1 ^ (2 * l - j + 1)) := by simp
    _ = (-1 : ℂ) ^ (j - 1 - l) * 1 := by simp
    _ = (-1 : ℂ) ^ (j - 1 - l) := by simp

set_option maxHeartbeats 400000 in

theorem gm_pos_signY' (l j a b : ℕ) (hlj : l < j) (h : j ≤ 2 * l) (ha : a = 2 * l - j)
    (hb : b = 0) (κ : ℂ) :
    (-1 : ℂ) ^ a * (-1 : ℂ) ^ b * -(κ * (-1 : ℂ) ^ (j - l - 1)) =
      κ * (-1 : ℂ) ^ (j - (j - 1 - l) - 1) := by
  subst ha
  subst hb
  simp
  have h_right_exp : j - (j - 1 - l) - 1 = l := by omega
  rw [h_right_exp]

  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlj

  have hdl : d + 1 ≤ l := by omega
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hdl

  have ha_eq : 2 * l - j = e := by omega
  have h_exp1 : j - l - 1 = d := by omega
  have hl_total : l = d + e + 1 := by omega
  rw [ha_eq, h_exp1, hl_total]

  have hRHS : (-1 : ℂ) ^ (d + e + 1) = (-1 : ℂ) ^ d * (-1 : ℂ) ^ e * (-1 : ℂ) := by
    calc
      (-1 : ℂ) ^ (d + e + 1) = (-1 : ℂ) ^ ((d + e) + 1) := by ring
      _ = (-1 : ℂ) ^ (d + e) * (-1 : ℂ) := by rw [pow_succ]
      _ = ((-1 : ℂ) ^ d * (-1 : ℂ) ^ e) * (-1 : ℂ) := by rw [pow_add]
      _ = (-1 : ℂ) ^ d * (-1 : ℂ) ^ e * (-1 : ℂ) := by ring
  rw [hRHS]
  ring

theorem gm_fam_add {c : ℕ → ℕ} {T : Type} [Group T] (G : EIdx c → ℂ → T) (e : EIdx c)
    (A A' : ℂ → T)
    (hGe : ∀ u, G e u = A u) (hGe' : ∀ u, G e.refl u = A' u)
    (hG0 : ∀ g u, g ≠ e → g ≠ e.refl → G g u = 1)
    (hA : ∀ u v, A u * A v = A (u + v)) (hA' : ∀ u v, A' u * A' v = A' (u + v)) :
    ∀ g u v, G g u * G g v = G g (u + v) := by
  intro g u v
  by_cases h : g = e
  · 
    rw [h, hGe, hGe, hGe]
    exact hA u v
  · 
    by_cases h' : g = e.refl
    · 
      rw [h', hGe', hGe', hGe']
      exact hA' u v
    · 
      rw [hG0 g u h h', hG0 g v h h', hG0 g (u + v) h h']
      simp

set_option maxHeartbeats 400000 in

theorem gm_fam_conj {c : ℕ → ℕ} {T : Type} [Group T] (G : EIdx c → ℂ → T) (e : EIdx c)
    (A A' : ℂ → T)
    (hGe : ∀ u, G e u = A u) (hGe' : ∀ u, G e.refl u = A' u)
    (hG0 : ∀ g u, g ≠ e → g ≠ e.refl → G g u = 1)
    (h : T) (μ : EIdx c → ℂ)
    (hA : ∀ u, h * A u * h⁻¹ = A (μ e * u)) (hA' : ∀ u, h * A' u * h⁻¹ = A' (μ e.refl * u)) :
    ∀ g u, h * G g u * h⁻¹ = G g (μ g * u) := by
  intro g u
  by_cases hge : g = e
  · rw [hge]
    rw [hGe u, hGe (μ e * u)]
    exact hA u
  · by_cases hgr : g = e.refl
    · rw [hgr]
      rw [hGe' u, hGe' (μ e.refl * u)]
      exact hA' u
    · have hg0u := hG0 g u hge hgr
      have hg0mu := hG0 g (μ g * u) hge hgr
      rw [hg0u, hg0mu]
      simp

theorem gm_fam_weyl {c : ℕ → ℕ} {T : Type} [Group T] (G : EIdx c → ℂ → T) (e : EIdx c)
    (A A' : ℂ → T)
    (hGe : ∀ u, G e u = A u) (hGe' : ∀ u, G e.refl u = A' u)
    (hG0 : ∀ g u, g ≠ e → g ≠ e.refl → G g u = 1)
    (h : T) (μ : EIdx c → ℂ)
    (hA : ∀ u, h * A u * h⁻¹ = A' (μ e * u)) (hA' : ∀ u, h * A' u * h⁻¹ = A (μ e.refl * u)) :
    ∀ g u, h * G g u * h⁻¹ = G g.refl (μ g * u) := by
  intro g u
  by_cases hge : g = e
  · subst hge
    rw [hGe u]
    rw [hA u]
    rw [hGe' (μ g * u)]
  · by_cases hgr : g = e.refl
    · subst hgr
      rw [hGe' u]
      rw [hA' u]
      rw [gm_refl_refl e]
      rw [hGe (μ e.refl * u)]
    · rw [hG0 g u hge hgr]
      simp
      have hgr_ne_e : g.refl ≠ e := by
        intro h_eq
        apply hgr
        calc
          g = g.refl.refl := (gm_refl_refl g).symm
          _ = e.refl := by rw [h_eq]
      have hgr_ne_erefl : g.refl ≠ e.refl := by
        intro h_eq
        apply hge
        calc
          g = g.refl.refl := (gm_refl_refl g).symm
          _ = e.refl.refl := by rw [h_eq]
          _ = e := gm_refl_refl e
      rw [hG0 g.refl (μ g * u) hgr_ne_e hgr_ne_erefl]

theorem gm_fam_comm1 {c : ℕ → ℕ} {T : Type} [Group T] (G : EIdx c → ℂ → T) (e : EIdx c)
    (A A' : ℂ → T)
    (hGe : ∀ u, G e u = A u) (hGe' : ∀ u, G e.refl u = A' u)
    (hG0 : ∀ g u, g ≠ e → g ≠ e.refl → G g u = 1)
    (h : ℂ → T) (P : EIdx c → Prop)
    (hA : P e → ∀ u v, h u * A v = A v * h u) (hA' : P e.refl → ∀ u v, h u * A' v = A' v * h u) :
    ∀ g, P g → ∀ u v, h u * G g v = G g v * h u := by
  intro g hg u v
  by_cases hge : g = e
  · subst hge
    rw [hGe v]
    exact hA hg u v
  by_cases hgrefl : g = e.refl
  · subst hgrefl
    rw [hGe' v]
    exact hA' hg u v
  have hGv : G g v = 1 := hG0 g v hge hgrefl
  rw [hGv]
  simp

set_option maxHeartbeats 400000 in

theorem gm_fam_U2 {c : ℕ → ℕ} {T : Type} [Group T] (G H : EIdx c → ℂ → T) (e : EIdx c)
    (A A' B B' : ℂ → T)
    (hGe : ∀ u, G e u = A u) (hGe' : ∀ u, G e.refl u = A' u)
    (hG0 : ∀ g u, g ≠ e → g ≠ e.refl → G g u = 1)
    (hHe : ∀ u, H e u = B u) (hHe' : ∀ u, H e.refl u = B' u)
    (hH0 : ∀ g u, g ≠ e → g ≠ e.refl → H g u = 1)
    (hAB' : 1 < Int.natAbs ((e.l : ℤ) - e.refl.l) → ∀ u v, A u * B' v = B' v * A u)
    (hA'B : 1 < Int.natAbs ((e.refl.l : ℤ) - e.l) → ∀ u v, A' u * B v = B v * A' u) :
    ∀ f g : EIdx c, (f.j ≠ g.j ∨ f.k ≠ g.k ∨ 1 < Int.natAbs ((f.l : ℤ) - g.l)) →
      ∀ u v, G f u * H g v = H g v * G f u := by
  intro f g hfg u v
  by_cases hf : f = e
  · 
    have hfg_e : e.j ≠ g.j ∨ e.k ≠ g.k ∨ 1 < Int.natAbs ((e.l : ℤ) - g.l) := by
      simpa [hf] using hfg
    rw [hf, hGe u]
    by_cases hg : g = e
    · 
      rw [hg] at hfg_e
      rcases hfg_e with (h | h | h)
      · exact (h rfl).elim
      · exact (h rfl).elim
      · have : Int.natAbs ((e.l : ℤ) - e.l) = 0 := by simp
        rw [this] at h
        omega
    · by_cases hg' : g = e.refl
      · 
        rw [hg'] at hfg_e
        rcases hfg_e with (h | h | h)
        · exact (h rfl).elim
        · exact (h rfl).elim
        · rw [hg', hHe' v]
          exact hAB' h u v
      · rw [hH0 g v hg hg']
        simp
  · by_cases hf' : f = e.refl
    · 
      have hfg_refl : e.refl.j ≠ g.j ∨ e.refl.k ≠ g.k ∨ 1 < Int.natAbs ((e.refl.l : ℤ) - g.l) := by
        simpa [hf'] using hfg
      rw [hf', hGe' u]
      by_cases hg : g = e
      · 
        rw [hg] at hfg_refl
        rcases hfg_refl with (h | h | h)
        · exact (h rfl).elim
        · exact (h rfl).elim
        · rw [hg, hHe v]
          exact hA'B h u v
      · by_cases hg' : g = e.refl
        · 
          rw [hg'] at hfg_refl
          rcases hfg_refl with (h | h | h)
          · exact (h rfl).elim
          · exact (h rfl).elim
          · have : Int.natAbs ((e.refl.l : ℤ) - e.refl.l) = 0 := by simp
            rw [this] at h
            omega
        · rw [hH0 g v hg hg']
          simp
    · 
      rw [hG0 f u hf hf']
      simp

set_option maxHeartbeats 400000 in

theorem gm_fam_XY {c : ℕ → ℕ} {T : Type} [Group T] (G H : EIdx c → ℂ → T) (e : EIdx c)
    (A A' B B' : ℂ → T)
    (hGe : ∀ u, G e u = A u) (hGe' : ∀ u, G e.refl u = A' u)
    (hG0 : ∀ g u, g ≠ e → g ≠ e.refl → G g u = 1)
    (hHe : ∀ u, H e u = B u) (hHe' : ∀ u, H e.refl u = B' u)
    (hH0 : ∀ g u, g ≠ e → g ≠ e.refl → H g u = 1)
    (hAB : ∀ s t : ℂˣ, B (-(t : ℂ)) * A (s : ℂ) * B (t : ℂ) =
      A (-((t⁻¹ : ℂˣ) : ℂ) / cst e.l e.j) * B (-(cst e.l e.j) * (t : ℂ) ^ 2 * s) *
        A (((t⁻¹ : ℂˣ) : ℂ) / cst e.l e.j))
    (hA'B' : ∀ s t : ℂˣ, B' (-(t : ℂ)) * A' (s : ℂ) * B' (t : ℂ) =
      A' (-((t⁻¹ : ℂˣ) : ℂ) / cst e.refl.l e.refl.j) *
        B' (-(cst e.refl.l e.refl.j) * (t : ℂ) ^ 2 * s) *
        A' (((t⁻¹ : ℂˣ) : ℂ) / cst e.refl.l e.refl.j)) :
    ∀ (g : EIdx c) (s t : ℂˣ), H g (-(t : ℂ)) * G g (s : ℂ) * H g (t : ℂ) =
      G g (-((t⁻¹ : ℂˣ) : ℂ) / cst g.l g.j) * H g (-(cst g.l g.j) * (t : ℂ) ^ 2 * s) *
        G g (((t⁻¹ : ℂˣ) : ℂ) / cst g.l g.j) := by
  intro g s t
  by_cases hg : g = e
  · subst hg
    simp only [hGe, hHe]
    exact hAB s t
  · by_cases hg' : g = e.refl
    · subst hg'
      simp only [hGe', hHe']
      exact hA'B' s t
    · simp only [hH0 g (-(t : ℂ)) hg hg',
                hG0 g (s : ℂ) hg hg',
                hH0 g (t : ℂ) hg hg',
                hG0 g (-((t⁻¹ : ℂˣ) : ℂ) / cst g.l g.j) hg hg',
                hH0 g (-(cst g.l g.j) * (t : ℂ) ^ 2 * (s : ℂ)) hg hg',
                hG0 g (((t⁻¹ : ℂˣ) : ℂ) / cst g.l g.j) hg hg',
                mul_one]

set_option maxHeartbeats 400000 in

theorem gm_rel_of {c : ℕ → ℕ} {T : Type} [Group T] (F : Gen c → T)
    (ρ : GL (Fin 2) ℂ →* T) (f0 : Gen c → GL (Fin 2) ℂ)
    (hgl : ∀ r, Rel c r → FreeGroup.lift f0 r = 1)
    (hH1 : ∀ s, F (Gen.H1 s) = ρ (f0 (Gen.H1 s))) (hH2 : ∀ s, F (Gen.H2 s) = ρ (f0 (Gen.H2 s)))
    (hXm : ∀ u, F (Gen.Xm u) = ρ (f0 (Gen.Xm u))) (hYm : ∀ u, F (Gen.Ym u) = ρ (f0 (Gen.Ym u)))
    (hXX : ∀ g u v, F (Gen.X g u) * F (Gen.X g v) = F (Gen.X g (u + v)))
    (hYY : ∀ g u v, F (Gen.Y g u) * F (Gen.Y g v) = F (Gen.Y g (u + v)))
    (hXY : ∀ (g : EIdx c) (s t : ℂˣ), F (Gen.Y g (-(t : ℂ))) * F (Gen.X g (s : ℂ)) *
      F (Gen.Y g (t : ℂ)) =
      F (Gen.X g (-((t⁻¹ : ℂˣ) : ℂ) / cst g.l g.j)) *
        F (Gen.Y g (-(cst g.l g.j) * (t : ℂ) ^ 2 * s)) *
        F (Gen.X g (((t⁻¹ : ℂˣ) : ℂ) / cst g.l g.j)))
    (hH1X : ∀ (s : ℂˣ) g u, F (Gen.H1 s) * F (Gen.X g u) * (F (Gen.H1 s))⁻¹ =
      F (Gen.X g ((s : ℂ) ^ (g.l + 1) * u)))
    (hH2X : ∀ (s : ℂˣ) g u, F (Gen.H2 s) * F (Gen.X g u) * (F (Gen.H2 s))⁻¹ =
      F (Gen.X g ((s : ℂ) ^ (g.j - g.l) * u)))
    (hH1Y : ∀ (s : ℂˣ) g u, F (Gen.H1 s) * F (Gen.Y g u) * (F (Gen.H1 s))⁻¹ =
      F (Gen.Y g (((s⁻¹ : ℂˣ) : ℂ) ^ (g.l + 1) * u)))
    (hH2Y : ∀ (s : ℂˣ) g u, F (Gen.H2 s) * F (Gen.Y g u) * (F (Gen.H2 s))⁻¹ =
      F (Gen.Y g (((s⁻¹ : ℂˣ) : ℂ) ^ (g.j - g.l) * u)))
    (hU1a : ∀ g : EIdx c, g.l = g.j - 1 → ∀ u v,
      F (Gen.Xm u) * F (Gen.X g v) = F (Gen.X g v) * F (Gen.Xm u))
    (hU1b : ∀ g : EIdx c, g.l = g.j - 1 → ∀ u v,
      F (Gen.Ym u) * F (Gen.Y g v) = F (Gen.Y g v) * F (Gen.Ym u))
    (hU1c : ∀ g : EIdx c, g.l = 0 → ∀ u v,
      F (Gen.Ym u) * F (Gen.X g v) = F (Gen.X g v) * F (Gen.Ym u))
    (hU1d : ∀ g : EIdx c, g.l = 0 → ∀ u v,
      F (Gen.Xm u) * F (Gen.Y g v) = F (Gen.Y g v) * F (Gen.Xm u))
    (hU2 : ∀ f g : EIdx c, (f.j ≠ g.j ∨ f.k ≠ g.k ∨ 1 < Int.natAbs ((f.l : ℤ) - g.l)) →
      ∀ u v, F (Gen.X f u) * F (Gen.Y g v) = F (Gen.Y g v) * F (Gen.X f u))
    (hU4a : ∀ g u, F (Gen.Xm 1) * F (Gen.Ym (-1)) * F (Gen.Xm 1) * F (Gen.X g u) *
      (F (Gen.Xm 1) * F (Gen.Ym (-1)) * F (Gen.Xm 1))⁻¹ =
        F (Gen.X g.refl ((-1 : ℂ) ^ g.l * u)))
    (hU4b : ∀ g u, F (Gen.Xm 1) * F (Gen.Ym (-1)) * F (Gen.Xm 1) * F (Gen.Y g u) *
      (F (Gen.Xm 1) * F (Gen.Ym (-1)) * F (Gen.Xm 1))⁻¹ =
        F (Gen.Y g.refl ((-1 : ℂ) ^ (g.j - g.l - 1) * u))) :
    ∀ r, Rel c r → FreeGroup.lift F r = 1 := by
  intro r hr
  cases hr
  · 
    rename_i s t
    have h := hgl _ (Rel.H1H1 s t)
    have h' := congrArg ρ h
    simpa [hH1, map_mul, map_inv, map_one] using h'
  · 
    rename_i s t
    have h := hgl _ (Rel.H2H2 s t)
    have h' := congrArg ρ h
    simpa [hH2, map_mul, map_inv, map_one] using h'
  · 
    rename_i s t
    have h := hgl _ (Rel.H1H2 s t)
    have h' := congrArg ρ h
    simpa [hH1, hH2, map_mul, map_inv, map_one] using h'
  · 
    rename_i u v
    have h := hgl _ (Rel.XX u v)
    have h' := congrArg ρ h
    simpa [hXm, map_mul, map_inv, map_one] using h'
  · 
    rename_i u v
    have h := hgl _ (Rel.YY u v)
    have h' := congrArg ρ h
    simpa [hYm, map_mul, map_inv, map_one] using h'
  · 
    rename_i s t
    have h := hgl _ (Rel.XY s t)
    have h' := congrArg ρ h
    simpa [hXm, hYm, map_mul, map_inv, map_one] using h'
  · 
    rename_i s
    have h := hgl _ (Rel.wwH s)
    have h' := congrArg ρ h
    simpa [hH1, hH2, hYm, hXm, wt, w, map_mul, map_inv, map_one] using h'
  · 
    rename_i u
    have h := hgl _ (Rel.wX u)
    have h' := congrArg ρ h
    simpa [hXm, hYm, w, map_mul, map_inv, map_one] using h'
  · 
    rename_i u
    have h := hgl _ (Rel.wY u)
    have h' := congrArg ρ h
    simpa [hXm, hYm, w, map_mul, map_inv, map_one] using h'
  · 
    rename_i s
    have h := hgl _ (Rel.wH1 s)
    have h' := congrArg ρ h
    simpa [hH1, hH2, hXm, hYm, w, map_mul, map_inv, map_one] using h'
  · 
    rename_i s
    have h := hgl _ (Rel.wH2 s)
    have h' := congrArg ρ h
    simpa [hH1, hH2, hXm, hYm, w, map_mul, map_inv, map_one] using h'
  · 
    rename_i s u
    have h := hgl _ (Rel.H1X s u)
    have h' := congrArg ρ h
    simpa [hH1, hXm, map_mul, map_inv, map_one] using h'
  · 
    rename_i s u
    have h := hgl _ (Rel.H2X s u)
    have h' := congrArg ρ h
    simpa [hH2, hXm, map_mul, map_inv, map_one] using h'
  · 
    rename_i s u
    have h := hgl _ (Rel.H1Y s u)
    have h' := congrArg ρ h
    simpa [hH1, hYm, map_mul, map_inv, map_one] using h'
  · 
    rename_i s u
    have h := hgl _ (Rel.H2Y s u)
    have h' := congrArg ρ h
    simpa [hH2, hYm, map_mul, map_inv, map_one] using h'
  · 
    rename_i e u v
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    have h := hXX e u v


    rw [h]
    simp
  · 
    rename_i e u v
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    have h := hYY e u v
    rw [h]
    simp
  · 
    rename_i e s t
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    have h := hXY e s t


    rw [h]
    group
  · 
    rename_i e s u
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    have h := hH1X s e u
    rw [h]
    simp
  · 
    rename_i e s u
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    have h := hH2X s e u
    rw [h]
    simp
  · 
    rename_i e s u
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    have h := hH1Y s e u
    rw [h]
    simp
  · 
    rename_i e s u
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    have h := hH2Y s e u
    rw [h]
    simp
  · 
    rename_i e he u v
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, GM.comm]
    have h := hU1a e he u v


    rw [h]
    simp [mul_assoc]
  · 
    rename_i e he u v
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, GM.comm]
    have h := hU1b e he u v
    rw [h]
    simp [mul_assoc]
  · 
    rename_i e he u v
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, GM.comm]
    have h := hU1c e he u v
    rw [h]
    simp [mul_assoc]
  · 
    rename_i e he u v
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, GM.comm]
    have h := hU1d e he u v
    rw [h]
    simp [mul_assoc]
  · 
    rename_i e f hef u v
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, GM.comm]
    have h := hU2 e f hef u v
    rw [h]
    simp [mul_assoc]
  · 
    rename_i e u
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, inv_one, Units.val_one]
    have h := hU4a e u
    rw [h]
    simp
  · 
    rename_i e u
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, inv_one, Units.val_one]
    have h := hU4b e u
    rw [h]
    simp
  · 
    rename_i s
    have h := hgl _ (Rel.U5a s)
    have h' := congrArg ρ h
    simpa [hXm, hYm, hH1, hH2, wt, w, map_mul, map_inv, map_one] using h'

theorem solution (c : ℕ → ℕ) :
    (∀ u : ℂ, u ≠ 0 → (PresentedGroup.of (Gen.Xm u) : Gm c) ≠ 1) ∧
    (∀ u : ℂ, u ≠ 0 → (PresentedGroup.of (Gen.Ym u) : Gm c) ≠ 1) ∧
    (∀ s : ℂˣ, s ≠ 1 → (PresentedGroup.of (Gen.H1 s) : Gm c) ≠ 1) ∧
    (∀ s : ℂˣ, s ≠ 1 → (PresentedGroup.of (Gen.H2 s) : Gm c) ≠ 1) ∧
    (∀ (e : EIdx c) (u : ℂ), u ≠ 0 → (PresentedGroup.of (Gen.X e u) : Gm c) ≠ 1) ∧
    (∀ (e : EIdx c) (u : ℂ), u ≠ 0 → (PresentedGroup.of (Gen.Y e u) : Gm c) ≠ 1) := by
  classical
  have hs := setting_real_part_nontrivial c
  -- the GL₂ realisation of the real part
  obtain ⟨f0, hf1, hf2, hfx, hfy, hfX, hfY⟩ : ∃ f0 : Gen c → GL (Fin 2) ℂ,
      (∀ s : ℂˣ, (f0 (Gen.H1 s) : Matrix (Fin 2) (Fin 2) ℂ) = !![(s : ℂ), 0; 0, 1]) ∧
      (∀ s : ℂˣ, (f0 (Gen.H2 s) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, (s : ℂ)]) ∧
      (∀ u : ℂ, (f0 (Gen.Xm u) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, u; 0, 1]) ∧
      (∀ u : ℂ, (f0 (Gen.Ym u) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; u, 1]) ∧
      (∀ (e : EIdx c) (u : ℂ), f0 (Gen.X e u) = 1) ∧
      (∀ (e : EIdx c) (u : ℂ), f0 (Gen.Y e u) = 1) := by
    let gx : ℂ → GL (Fin 2) ℂ := fun u =>
      ⟨!![1, u; 0, 1], !![1, -u; 0, 1], by simp [Matrix.one_fin_two],
        by simp [Matrix.one_fin_two]⟩
    let gy : ℂ → GL (Fin 2) ℂ := fun u =>
      ⟨!![1, 0; u, 1], !![1, 0; -u, 1], by simp [Matrix.one_fin_two],
        by simp [Matrix.one_fin_two]⟩
    let g1 : ℂˣ → GL (Fin 2) ℂ := fun s =>
      ⟨!![(s : ℂ), 0; 0, 1], !![((s⁻¹ : ℂˣ) : ℂ), 0; 0, 1], by simp [Matrix.one_fin_two],
        by simp [Matrix.one_fin_two]⟩
    let g2 : ℂˣ → GL (Fin 2) ℂ := fun s =>
      ⟨!![1, 0; 0, (s : ℂ)], !![1, 0; 0, ((s⁻¹ : ℂˣ) : ℂ)], by simp [Matrix.one_fin_two],
        by simp [Matrix.one_fin_two]⟩
    exact ⟨fun g => match g with
      | .H1 s => g1 s
      | .H2 s => g2 s
      | .Xm u => gx u
      | .Ym u => gy u
      | .X _ _ => 1
      | .Y _ _ => 1, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl⟩
  have hgl : ∀ r, Rel c r → FreeGroup.lift f0 r = 1 := gm_gl2_rel c f0 hf1 hf2 hfx hfy hfX hfY
  -- the substitution action of GL₂ on ℂ[X0, X1, Z]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : GL (Fin 2) ℂ →*
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ),
      ∀ (g : GL (Fin 2) ℂ) (f : MvPolynomial (Fin 3) ℂ), ρ g f =
        MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
            (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
          (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
            (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
          (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
            Fin 3 → MvPolynomial (Fin 3) ℂ) f := by
    let ρ0 : GL (Fin 2) ℂ → (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ) := fun g =>
      LinearEquiv.ofLinear
        (MvPolynomial.aeval (![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 • MvPolynomial.X 0 +
            (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
          (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
            (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
          (g : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
            Fin 3 → MvPolynomial (Fin 3) ℂ)).toLinearMap
        (MvPolynomial.aeval (![((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 •
              MvPolynomial.X 0 +
            ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 • MvPolynomial.X 1,
          ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 • MvPolynomial.X 0 +
            ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 • MvPolynomial.X 1,
          ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det • MvPolynomial.X 2] :
            Fin 3 → MvPolynomial (Fin 3) ℂ)).toLinearMap
        (LinearMap.ext fun f => by
          simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
            LinearMap.id_coe, id_eq]
          rw [gm_aeval_subst_mul, mul_inv_cancel, gm_aeval_subst_one])
        (LinearMap.ext fun f => by
          simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
            LinearMap.id_coe, id_eq]
          rw [gm_aeval_subst_mul, inv_mul_cancel, gm_aeval_subst_one])
    refine ⟨MonoidHom.mk' ρ0 (fun g h => LinearEquiv.ext fun f => ?_), fun g f => rfl⟩
    simp only [ρ0, LinearEquiv.mul_apply, LinearEquiv.ofLinear_apply, AlgHom.toLinearMap_apply]
    rw [gm_aeval_subst_mul]
  -- the monomial transvections
  obtain ⟨τ, hτ⟩ : ∃ τ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) → ℂ →
      (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ),
      ∀ p q : Fin 3 →₀ ℕ, p ≠ q → ∀ (u : ℂ) (v : MvPolynomial (Fin 3) ℂ),
        τ p q u v = v + (u * MvPolynomial.coeff q v) • MvPolynomial.monomial p (1 : ℂ) := by
    refine ⟨fun p q u => if h : p = q then 1 else LinearEquiv.ofLinear
      (LinearMap.id + u • (MvPolynomial.lcoeff ℂ q).smulRight (MvPolynomial.monomial p (1 : ℂ)))
      (LinearMap.id + (-u) • (MvPolynomial.lcoeff ℂ q).smulRight
        (MvPolynomial.monomial p (1 : ℂ)))
      (gm_L_inv p q h u (-u) (by ring)) (gm_L_inv p q h (-u) u (by ring)), ?_⟩
    intro p q h u v
    simp only [dif_neg h, LinearEquiv.ofLinear_apply, LinearMap.add_apply, LinearMap.id_coe,
      id_eq, LinearMap.smul_apply, LinearMap.smulRight_apply, MvPolynomial.lcoeff_apply,
      smul_smul]
  -- the representation attached to e and a choice of monomials and scalars
  have general : ∀ (e : EIdx c) (p q p' q' : Fin 3 →₀ ℕ) (α β α' β' : ℂ),
      p ≠ q → p' ≠ q' →
      α * β = cst e.l e.j → α' * β' = cst e.refl.l e.refl.j →
      p 0 + p 2 = q 0 + q 2 + (e.l + 1) → p 1 + p 2 = q 1 + q 2 + (e.j - e.l) →
      p' 0 + p' 2 = q' 0 + q' 2 + (e.refl.l + 1) →
      p' 1 + p' 2 = q' 1 + q' 2 + (e.refl.j - e.refl.l) →
      p' 0 = p 1 → p' 1 = p 0 → p' 2 = p 2 → q' 0 = q 1 → q' 1 = q 0 → q' 2 = q 2 →
      (-1 : ℂ) ^ (p 0) * (-1 : ℂ) ^ (q 0) * α = α' * (-1 : ℂ) ^ e.l →
      (-1 : ℂ) ^ (q 0) * (-1 : ℂ) ^ (p 0) * β = β' * (-1 : ℂ) ^ (e.j - e.l - 1) →
      (-1 : ℂ) ^ (p' 0) * (-1 : ℂ) ^ (q' 0) * α' = α * (-1 : ℂ) ^ e.refl.l →
      (-1 : ℂ) ^ (q' 0) * (-1 : ℂ) ^ (p' 0) * β' =
        β * (-1 : ℂ) ^ (e.refl.j - e.refl.l - 1) →
      (e.l = e.j - 1 → p 1 = 0 ∧ q 0 = 0) → (e.l = 0 → p 0 = 0 ∧ q 1 = 0) →
      (e.refl.l = e.refl.j - 1 → p' 1 = 0 ∧ q' 0 = 0) →
      (e.refl.l = 0 → p' 0 = 0 ∧ q' 1 = 0) →
      (1 < Int.natAbs ((e.l : ℤ) - e.refl.l) → p ≠ p' ∧ q ≠ q') →
      (e.refl = e → p' = p ∧ q' = q ∧ α' = α ∧ β' = β) →
      ∀ u : ℂ, u ≠ 0 →
        ((PresentedGroup.of (Gen.X e u) : Gm c) ≠ 1 ∧
          (PresentedGroup.of (Gen.Y e u) : Gm c) ≠ 1) ∧
        ((PresentedGroup.of (Gen.X e.refl u) : Gm c) ≠ 1 ∧
          (PresentedGroup.of (Gen.Y e.refl u) : Gm c) ≠ 1) := by
    intro e p q p' q' α β α' β' hpq hpq' hab hab' hw1 hw2 hw1' hw2' hs0 hs1 hs2 ht0 ht1 ht2
      sX sY sX' sY' hA hB hA' hB' hU2 hself
    have hc : cst e.l e.j ≠ 0 := gm_cst_ne_zero _ _ e.hl
    have hc' : cst e.refl.l e.refl.j ≠ 0 := gm_cst_ne_zero _ _ e.refl.hl
    have hα : α ≠ 0 := left_ne_zero_of_mul (hab ▸ hc)
    have hβ : β ≠ 0 := right_ne_zero_of_mul (hab ▸ hc)
    have hα' : α' ≠ 0 := left_ne_zero_of_mul (hab' ▸ hc')
    have hβ' : β' ≠ 0 := right_ne_zero_of_mul (hab' ▸ hc')
    let F : Gen c → (MvPolynomial (Fin 3) ℂ ≃ₗ[ℂ] MvPolynomial (Fin 3) ℂ) := fun g =>
      match g with
      | .H1 s => ρ (f0 (.H1 s))
      | .H2 s => ρ (f0 (.H2 s))
      | .Xm u => ρ (f0 (.Xm u))
      | .Ym u => ρ (f0 (.Ym u))
      | .X g u => if g = e then τ p q (α * u) else if g = e.refl then τ p' q' (α' * u) else 1
      | .Y g u => if g = e then τ q p (β * u) else if g = e.refl then τ q' p' (β' * u) else 1
    have hXe : ∀ u, F (.X e u) = τ p q (α * u) := fun u => if_pos rfl
    have hYe : ∀ u, F (.Y e u) = τ q p (β * u) := fun u => if_pos rfl
    have hXe' : ∀ u, F (.X e.refl u) = τ p' q' (α' * u) := by
      intro u
      by_cases h : e.refl = e
      · obtain ⟨h1, h2, h3, _⟩ := hself h
        show (if e.refl = e then _ else _) = _
        rw [if_pos h, h1, h2, h3]
      · show (if e.refl = e then _ else _) = _
        rw [if_neg h, if_pos rfl]
    have hYe' : ∀ u, F (.Y e.refl u) = τ q' p' (β' * u) := by
      intro u
      by_cases h : e.refl = e
      · obtain ⟨h1, h2, _, h4⟩ := hself h
        show (if e.refl = e then _ else _) = _
        rw [if_pos h, h1, h2, h4]
      · show (if e.refl = e then _ else _) = _
        rw [if_neg h, if_pos rfl]
    have hX0 : ∀ g u, g ≠ e → g ≠ e.refl → F (.X g u) = 1 := fun g u h1 h2 => by
      show (if g = e then _ else _) = _
      rw [if_neg h1, if_neg h2]
    have hY0 : ∀ g u, g ≠ e → g ≠ e.refl → F (.Y g u) = 1 := fun g u h1 h2 => by
      show (if g = e then _ else _) = _
      rw [if_neg h1, if_neg h2]
    -- the Weyl element
    have hgW := gm_weyl_matrix (f0 (.Xm 1)) (f0 (.Ym (-1))) (hfx 1) (hfy (-1))
    have hFw : F (.Xm 1) * F (.Ym (-1)) * F (.Xm 1) =
        ρ (f0 (.Xm 1) * f0 (.Ym (-1)) * f0 (.Xm 1)) := by
      simp only [map_mul]; rfl
    have hU2' : 1 < Int.natAbs ((e.refl.l : ℤ) - e.l) → p' ≠ p ∧ q' ≠ q := fun h => by
      rw [← Int.natAbs_neg, neg_sub] at h
      exact ⟨(hU2 h).1.symm, (hU2 h).2.symm⟩
    -- the relations of Gm c hold for F
    have hrel : ∀ r ∈ {r : FreeGroup (Gen c) | Rel c r}, FreeGroup.lift F r = 1 :=
      fun r hr => gm_rel_of F ρ f0 hgl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl)
        (gm_fam_add (fun g u => F (.X g u)) e (fun u => τ p q (α * u))
          (fun u => τ p' q' (α' * u)) hXe hXe' hX0
          (fun u v => by beta_reduce; rw [gm_tau_add τ hτ p q hpq, mul_add])
          (fun u v => by beta_reduce; rw [gm_tau_add τ hτ p' q' hpq', mul_add]))
        (gm_fam_add (fun g u => F (.Y g u)) e (fun u => τ q p (β * u))
          (fun u => τ q' p' (β' * u)) hYe hYe' hY0
          (fun u v => by beta_reduce; rw [gm_tau_add τ hτ q p hpq.symm, mul_add])
          (fun u v => by beta_reduce; rw [gm_tau_add τ hτ q' p' hpq'.symm, mul_add]))
        (gm_fam_XY (fun g u => F (.X g u)) (fun g u => F (.Y g u)) e (fun u => τ p q (α * u))
          (fun u => τ p' q' (α' * u)) (fun u => τ q p (β * u)) (fun u => τ q' p' (β' * u))
          hXe hXe' hX0 hYe hYe' hY0
          (gm_tau_sl2 τ hτ p q hpq α β _ hab hc)
          (gm_tau_sl2 τ hτ p' q' hpq' α' β' _ hab' hc'))
        (fun s => gm_fam_conj (fun g u => F (.X g u)) e (fun u => τ p q (α * u))
          (fun u => τ p' q' (α' * u)) hXe hXe' hX0 (F (.H1 s)) (fun g => (s : ℂ) ^ (g.l + 1))
          (gm_conj_diag ρ hρ τ hτ _ (s : ℂ) 1 s.ne_zero one_ne_zero (hf1 s) p q hpq _ α
            (by rw [hw1]; ring))
          (gm_conj_diag ρ hρ τ hτ _ (s : ℂ) 1 s.ne_zero one_ne_zero (hf1 s) p' q' hpq' _ α'
            (by rw [hw1']; ring)))
        (fun s => gm_fam_conj (fun g u => F (.X g u)) e (fun u => τ p q (α * u))
          (fun u => τ p' q' (α' * u)) hXe hXe' hX0 (F (.H2 s)) (fun g => (s : ℂ) ^ (g.j - g.l))
          (gm_conj_diag ρ hρ τ hτ _ 1 (s : ℂ) one_ne_zero s.ne_zero (hf2 s) p q hpq _ α
            (by rw [hw2]; ring))
          (gm_conj_diag ρ hρ τ hτ _ 1 (s : ℂ) one_ne_zero s.ne_zero (hf2 s) p' q' hpq' _ α'
            (by rw [hw2']; ring)))
        (fun s => gm_fam_conj (fun g u => F (.Y g u)) e (fun u => τ q p (β * u))
          (fun u => τ q' p' (β' * u)) hYe hYe' hY0 (F (.H1 s))
          (fun g => ((s⁻¹ : ℂˣ) : ℂ) ^ (g.l + 1))
          (gm_conj_diag ρ hρ τ hτ _ (s : ℂ) 1 s.ne_zero one_ne_zero (hf1 s) q p hpq.symm _ β
            (by rw [hw1]; simp only [one_pow, mul_one, one_mul, Units.val_inv_eq_inv_val, inv_pow]; exact gm_pow_inv_mul _ s.ne_zero _ _))
          (gm_conj_diag ρ hρ τ hτ _ (s : ℂ) 1 s.ne_zero one_ne_zero (hf1 s) q' p' hpq'.symm _ β'
            (by rw [hw1']; simp only [one_pow, mul_one, one_mul, Units.val_inv_eq_inv_val, inv_pow]; exact gm_pow_inv_mul _ s.ne_zero _ _)))
        (fun s => gm_fam_conj (fun g u => F (.Y g u)) e (fun u => τ q p (β * u))
          (fun u => τ q' p' (β' * u)) hYe hYe' hY0 (F (.H2 s))
          (fun g => ((s⁻¹ : ℂˣ) : ℂ) ^ (g.j - g.l))
          (gm_conj_diag ρ hρ τ hτ _ 1 (s : ℂ) one_ne_zero s.ne_zero (hf2 s) q p hpq.symm _ β
            (by rw [hw2]; simp only [one_pow, mul_one, one_mul, Units.val_inv_eq_inv_val, inv_pow]; exact gm_pow_inv_mul _ s.ne_zero _ _))
          (gm_conj_diag ρ hρ τ hτ _ 1 (s : ℂ) one_ne_zero s.ne_zero (hf2 s) q' p' hpq'.symm _ β'
            (by rw [hw2']; simp only [one_pow, mul_one, one_mul, Units.val_inv_eq_inv_val, inv_pow]; exact gm_pow_inv_mul _ s.ne_zero _ _)))
        (gm_fam_comm1 (fun g u => F (.X g u)) e (fun u => τ p q (α * u))
          (fun u => τ p' q' (α' * u)) hXe hXe' hX0 (fun u => F (.Xm u))
          (fun g => g.l = g.j - 1)
          (fun h u v => gm_comm_ux ρ hρ τ hτ _ u (hfx u) p q hpq (hA h).1 (hA h).2 _)
          (fun h u v => gm_comm_ux ρ hρ τ hτ _ u (hfx u) p' q' hpq' (hA' h).1 (hA' h).2 _))
        (gm_fam_comm1 (fun g u => F (.Y g u)) e (fun u => τ q p (β * u))
          (fun u => τ q' p' (β' * u)) hYe hYe' hY0 (fun u => F (.Ym u))
          (fun g => g.l = g.j - 1)
          (fun h u v => gm_comm_uy ρ hρ τ hτ _ u (hfy u) q p hpq.symm (hA h).2 (hA h).1 _)
          (fun h u v => gm_comm_uy ρ hρ τ hτ _ u (hfy u) q' p' hpq'.symm (hA' h).2 (hA' h).1 _))
        (gm_fam_comm1 (fun g u => F (.X g u)) e (fun u => τ p q (α * u))
          (fun u => τ p' q' (α' * u)) hXe hXe' hX0 (fun u => F (.Ym u))
          (fun g => g.l = 0)
          (fun h u v => gm_comm_uy ρ hρ τ hτ _ u (hfy u) p q hpq (hB h).1 (hB h).2 _)
          (fun h u v => gm_comm_uy ρ hρ τ hτ _ u (hfy u) p' q' hpq' (hB' h).1 (hB' h).2 _))
        (gm_fam_comm1 (fun g u => F (.Y g u)) e (fun u => τ q p (β * u))
          (fun u => τ q' p' (β' * u)) hYe hYe' hY0 (fun u => F (.Xm u))
          (fun g => g.l = 0)
          (fun h u v => gm_comm_ux ρ hρ τ hτ _ u (hfx u) q p hpq.symm (hB h).2 (hB h).1 _)
          (fun h u v => gm_comm_ux ρ hρ τ hτ _ u (hfx u) q' p' hpq'.symm (hB' h).2 (hB' h).1 _))
        (gm_fam_U2 (fun g u => F (.X g u)) (fun g u => F (.Y g u)) e (fun u => τ p q (α * u))
          (fun u => τ p' q' (α' * u)) (fun u => τ q p (β * u)) (fun u => τ q' p' (β' * u))
          hXe hXe' hX0 hYe hYe' hY0
          (fun h u v => gm_tau_comm τ hτ p q p' q' hpq hpq' (hU2 h).1 (hU2 h).2 _ _)
          (fun h u v => gm_tau_comm τ hτ p' q' p q hpq' hpq (hU2' h).1 (hU2' h).2 _ _))
        (fun g u => by
          rw [hFw]
          exact gm_fam_weyl (fun g u => F (.X g u)) e (fun u => τ p q (α * u))
            (fun u => τ p' q' (α' * u)) hXe hXe' hX0 _ (fun g => (-1 : ℂ) ^ g.l)
            (gm_conj_W ρ hρ τ hτ _ hgW p q p' q' hpq hpq' hs0 hs1 hs2 ht0 ht1 ht2 α α' _ sX)
            (gm_conj_W ρ hρ τ hτ _ hgW p' q' p q hpq' hpq hs1.symm hs0.symm hs2.symm
              ht1.symm ht0.symm ht2.symm α' α _ sX') g u)
        (fun g u => by
          rw [hFw]
          exact gm_fam_weyl (fun g u => F (.Y g u)) e (fun u => τ q p (β * u))
            (fun u => τ q' p' (β' * u)) hYe hYe' hY0 _ (fun g => (-1 : ℂ) ^ (g.j - g.l - 1))
            (gm_conj_W ρ hρ τ hτ _ hgW q p q' p' hpq.symm hpq'.symm ht0 ht1 ht2 hs0 hs1 hs2
              β β' _ sY)
            (gm_conj_W ρ hρ τ hτ _ hgW q' p' q p hpq'.symm hpq.symm ht1.symm ht0.symm ht2.symm
              hs1.symm hs0.symm hs2.symm β' β _ sY') g u)
        r hr
    -- the homomorphism out of Gm c and the nontriviality of the images
    have hφ : ∀ g, PresentedGroup.toGroup hrel (PresentedGroup.of g) = F g :=
      fun g => PresentedGroup.toGroup.of hrel
    have key : ∀ (z : Gen c), F z ≠ 1 → (PresentedGroup.of z : Gm c) ≠ 1 := by
      intro z hz h
      apply hz
      rw [← hφ, h, map_one]
    intro u hu
    refine ⟨⟨key _ ?_, key _ ?_⟩, key _ ?_, key _ ?_⟩
    · rw [hXe]; exact gm_tau_ne_one τ hτ p q hpq _ (mul_ne_zero hα hu)
    · rw [hYe]; exact gm_tau_ne_one τ hτ q p hpq.symm _ (mul_ne_zero hβ hu)
    · rw [hXe']; exact gm_tau_ne_one τ hτ p' q' hpq' _ (mul_ne_zero hα' hu)
    · rw [hYe']; exact gm_tau_ne_one τ hτ q' p' hpq'.symm _ (mul_ne_zero hβ' hu)
  -- case 2l+1 > j: the monomials X0 Z^l, X1^(2l-j) and their Weyl images
  have pos : ∀ e : EIdx c, e.j ≤ 2 * e.l → ∀ u : ℂ, u ≠ 0 →
      ((PresentedGroup.of (Gen.X e u) : Gm c) ≠ 1 ∧
        (PresentedGroup.of (Gen.Y e u) : Gm c) ≠ 1) ∧
      ((PresentedGroup.of (Gen.X e.refl u) : Gm c) ≠ 1 ∧
        (PresentedGroup.of (Gen.Y e.refl u) : Gm c) ≠ 1) := by
    intro e h
    have hl := e.hl
    have hrl : e.refl.l = e.j - 1 - e.l := rfl
    have hrj : e.refl.j = e.j := rfl
    refine general e (Finsupp.single 0 1 + Finsupp.single 2 e.l)
      (Finsupp.single 1 (2 * e.l - e.j)) (Finsupp.single 1 1 + Finsupp.single 2 e.l)
      (Finsupp.single 0 (2 * e.l - e.j)) 1 (cst e.l e.j) ((-1 : ℂ) ^ (e.l + 1))
      (-(cst e.l e.j * (-1 : ℂ) ^ (e.j - e.l - 1))) ?_ ?_ (one_mul _)
      (gm_pos_cst e.l e.j hl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (gm_pos_signX e.l _ _ (by simp) (by simp))
      (gm_pos_signY e.l e.j _ _ (by simp) (by simp) _)
      (gm_pos_signX' e.l e.j _ _ hl h (by simp) (by simp))
      (gm_pos_signY' e.l e.j _ _ hl h (by simp) (by simp) _) ?_ ?_ ?_ ?_ ?_ ?_
    · intro hh; have := congrArg (fun m => m 0) hh; simp at this
    · intro hh; have := congrArg (fun m => m 1) hh; simp at this
    · simp; omega
    · simp; omega
    · simp [hrl]; omega
    · simp [hrl, hrj]; omega
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · intro _; simp
    · intro h0; exfalso; omega
    · intro h0; exfalso; rw [hrl, hrj] at h0; omega
    · intro _; simp
    · intro h0
      rw [hrl] at h0
      refine ⟨fun hh => ?_, fun hh => ?_⟩
      · have := congrArg (fun m => m 0) hh; simp at this
      · have := congrArg (fun m => m 1) hh; simp at this; omega
    · intro h0; exfalso
      have := congrArg EIdx.l h0
      rw [hrl] at this; omega
  -- case 2l+1 = j (then e.refl = e): the monomial (X0 X1)^l Z against 1
  have zero : ∀ e : EIdx c, e.j = 2 * e.l + 1 → ∀ u : ℂ, u ≠ 0 →
      (PresentedGroup.of (Gen.X e u) : Gm c) ≠ 1 ∧
        (PresentedGroup.of (Gen.Y e u) : Gm c) ≠ 1 := by
    intro e h u hu
    have hrl : e.refl.l = e.l := by show e.j - 1 - e.l = e.l; omega
    have hrj : e.refl.j = e.j := rfl
    have hjl : e.j - e.l - 1 = e.l := by omega
    refine (general e (Finsupp.single 0 e.l + Finsupp.single 1 e.l + Finsupp.single 2 1) 0
      (Finsupp.single 0 e.l + Finsupp.single 1 e.l + Finsupp.single 2 1) 0 1 (cst e.l e.j) 1
      (cst e.l e.j) ?_ ?_ (one_mul _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ u hu).1
    · intro hh; have := congrArg (fun m => m 2) hh; simp at this
    · intro hh; have := congrArg (fun m => m 2) hh; simp at this
    · rw [hrl, hrj, one_mul]
    · simp
    · simp; omega
    · simp [hrl]
    · simp [hrl, hrj]; omega
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [hjl]; ring
    · simp [hrl]
    · rw [hrl, hrj, hjl]; simp; ring
    · intro h0; simp; omega
    · intro h0; simp [h0]
    · intro h0; rw [hrl, hrj] at h0; simp; omega
    · intro h0; rw [hrl] at h0; simp [h0]
    · intro h0; rw [hrl] at h0; simp at h0
    · intro _; exact ⟨rfl, rfl, rfl, rfl⟩
  have key : ∀ (e : EIdx c) (u : ℂ), u ≠ 0 →
      (PresentedGroup.of (Gen.X e u) : Gm c) ≠ 1 ∧
        (PresentedGroup.of (Gen.Y e u) : Gm c) ≠ 1 := by
    intro e u hu
    rcases lt_trichotomy (2 * e.l + 1) e.j with hlt | heq | hgt
    · have := (pos e.refl (by show e.j ≤ 2 * (e.j - 1 - e.l); omega) u hu).2
      rwa [gm_refl_refl] at this
    · exact zero e heq.symm u hu
    · exact (pos e (by omega) u hu).1
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, fun e u hu => (key e u hu).1,
    fun e u hu => (key e u hu).2⟩
