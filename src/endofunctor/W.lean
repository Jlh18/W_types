import constructions
import endofunctor.algebra

universes u₀ u₁

namespace category_theory

namespace W_type
open endofunctor

/-
We fix a W-type consisting of an index α of constructors and
their dependently indexed arities β.
-/
variables {α : Type u₀} (β : α → Type u₁)

/-- The polynomial endofunctor associated to a `W_type` -/
@[simps] def polynomial_endofunctor : Type (max u₀ u₁) ⥤ Type (max u₀ u₁) :=
{ obj := λ X, Σ (a : α), β a → X,
  map := λ X Y f p, ⟨ p.1 , f ∘ p.2 ⟩ }

/-- The category of W_types -/
@[nolint check_univs]
structure cat :=
{α : Type*}
(β : α → Type*)

/-- Polynomial endofunctors form a full subcategory of `C ⥤ C` -/
instance : category cat :=
{ hom := λ W₀ W₁, nat_trans (polynomial_endofunctor W₀.β) (polynomial_endofunctor W₁.β),
  id := λ _, nat_trans.id _,
  comp := λ _ _ _, nat_trans.vcomp }

namespace cat

/-- Two W_types are isomorphic if their endofunctors are isomorphic -/
def iso_of_iso {W₀ W₁ : cat} (endo_iso : polynomial_endofunctor W₀.β ≅ polynomial_endofunctor W₁.β) :
  W₀ ≅ W₁ :=
{ hom := endo_iso.hom,
  inv := endo_iso.inv,
  hom_inv_id' := endo_iso.hom_inv_id,
  inv_hom_id' := endo_iso.inv_hom_id }.

/-- Two W_types are isomorphic if their defining types are equivalent -/
def iso_of_equiv {W₀ W₁ : cat} (hα : W₀.α ≃ W₁.α) (hβ : ∀ a : W₀.α, W₀.β a ≃ W₁.β (hα.to_fun a)) :
  W₀ ≅ W₁ :=
iso_of_iso $ nat_iso.of_components
  (λ X, equiv.to_iso $ equiv.sigma_congr hα (λ a, equiv.Pi_congr' (hβ _) (by { intro, refl })))
  (by { intros, funext,
    simp only [types_comp_apply, equiv.to_iso, equiv.sigma_congr, equiv.to_fun_as_coe,
      equiv.coe_trans, function.comp_app, equiv.sigma_congr_right_apply, equiv.coe_Pi_congr',
      polynomial_endofunctor_map_snd, equiv.coe_refl, id.def, equiv.sigma_congr_left_apply],
    dsimp only [polynomial_endofunctor],
    simp [equiv.Pi_congr'_apply] })

open endofunctor.algebra

/-- If the `W_types` are isomorphic then their algebra categories are equivalent -/
def iso_to_equivalence {W₀ W₁ : cat} (hiso : W₀ ≅ W₁) :
algebra (polynomial_endofunctor W₀.β) ≌ algebra (polynomial_endofunctor W₁.β) :=
{ functor := functor_of_nat_trans hiso.inv,
  inverse := functor_of_nat_trans hiso.hom,
  unit_iso := functor_of_nat_trans_id.symm ≪≫
    functor_of_nat_trans_eq hiso.3.symm ≪≫ (functor_of_nat_trans_comp _ _),
  counit_iso := (functor_of_nat_trans_comp _ _).symm ≪≫
    functor_of_nat_trans_eq hiso.4 ≪≫ functor_of_nat_trans_id }

/--
The endofunctor `Σ (x : γ), X ^ (fin n) ≃ γ X ^ n `
-/
@[simp] def monomial (γ : Type u₀) (n : ℕ) : cat := ⟨ λ x : γ, ulift (fin n) ⟩

/--
The identity endofunctor as a W_type,
`X ≃ punit X ^ 1`
-/
@[simp] def X : cat := monomial punit 1

/--
The polynomial endofunctor taking anything to `⊥_ = pempty`,
since `pempty ≃ pempty X ^ 0` -/
@[simps] instance : has_zero cat := { zero := monomial pempty 0 }

instance : inhabited cat := ⟨ 0 ⟩

/--
The polynomial endofunctor taking anything to `⊤_ = punit`,
since `punit ≃ punit X ^ 0`
-/
@[simps] instance : has_one cat := { one := monomial punit 0 }

/--
The constant functor going to a type `γ` is a polynomial
`γ = Σ (a : γ) 1 = Σ (a : γ) X ^ pempty `
-/
instance : has_coe (Type u₀) cat.{u₀ u₀} := { coe := λ γ, monomial γ 0 }

@[simp] lemma coe_β_eq (γ : Type u₀) :
  (γ : cat.{u₀ u₀}).β = λ (_ : γ), ulift (fin 0) := rfl

/--
The sum of two polynomial endofunctors
`Σ (a : α₀) X^(β a) + Σ (a : α₁) X^(β₁ a) ≃ Σ (a : α₀ ⊕ α₁) X^((β₀ ⊕ β₁) a)`
-/
@[simps] def addition : cat.{u₁ u₀} → cat.{u₁ u₀} → cat.{u₁ u₀} :=
λ W₀ W₁, ⟨ sum.elim W₀.β W₁.β ⟩

@[simps] instance : has_add cat := { add := addition }

end cat

/-- `W_type` β as an algebra of its associated polynomial endofunctor -/
def as_algebra : algebra (polynomial_endofunctor β) :=
{ A   := W_type β,
  str := W_type.of_sigma }

variables {β} (A : algebra (polynomial_endofunctor β))

/-- The map in `Type` from the initial algebra `W_type` to any other algebra -/
def lift_f : W_type β → A.A
| (W_type.mk a b) := A.str ⟨ a , λ x, lift_f (b x) ⟩

/-- The map in `endofunctor.algebra` from the initial algebra `W_type` to any other algebra -/
def lift : as_algebra β ⟶ A := { f := lift_f A }

lemma lift_uniq (f : as_algebra β ⟶ A) : f = lift A :=
begin
  ext w,
  induction w with a b hw,
  simp only [lift, lift_f],
  convert (congr_fun f.2 ⟨ a , b ⟩).symm,
  funext x,
  exact (hw x).symm,
end

instance (A : algebra (polynomial_endofunctor β)) : unique (as_algebra β ⟶ A) :=
{ default := lift A,
  uniq := lift_uniq A }.

/-- A `W_Type` is the initial algebra of its associated polynomial endofunctor -/
def is_initial : limits.is_initial (as_algebra β) :=
limits.is_initial.of_unique _

section instances

open _root_.W_type cat

/-- The polynomial endofunctor of the `W_type` for `ℕ` is `1 + X` (a.k.a the maybe monad) -/
def cat_nat_β_eq_one_add_X : cat.mk nat_β ≅ 1 + X :=
iso_of_equiv (nat_α_equiv_bool.trans equiv.bool_equiv_punit_sum_punit)
  (λ c, match c with
    | nat_α.zero := by {dsimp [nat_β, equiv.bool_equiv_punit_sum_punit, nat_α_equiv_bool],
      exact (equiv.equiv_empty _).symm }
    | nat_α.succ := by {dsimp [nat_β, equiv.bool_equiv_punit_sum_punit, nat_α_equiv_bool],
      exact equiv_of_unique_of_unique }
    end)

/-- The polynomial endofunctor for the `W_type` for `list γ` is `1 + γ X` -/
def cat_list_β_eq_one_add_type (γ : Type u₁) : cat.mk (list_β γ) ≅ 1 + monomial γ 1 :=
iso_of_equiv (list_α_equiv_punit_sum γ)
  (λ c, match c with
    | list_α.nil := by { dsimp [list_β, list_α_equiv_punit_sum],
      exact (equiv.equiv_pempty _).symm }
    | list_α.cons x := by { dsimp [list_β, list_α_equiv_punit_sum],
      exact equiv_of_unique_of_unique }
    end)

end instances

end W_type

end category_theory
