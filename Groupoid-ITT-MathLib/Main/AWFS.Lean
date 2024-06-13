import Main.Arrows
import Main.Triangle
import Mathlib.CategoryTheory.Whiskering

namespace CategoryTheory.Factorization

universe v v₂ u u₂

open CategoryTheory.Diagrams
open WalkingTriangleHom
open WalkingArrowHom

variable {C : Type u} [Category.{v} C]

def MiddleFunctor : WalkingArrow ⥤ WalkingTriangle where
  obj x := match x with
    | WalkingArrow.zero => WalkingTriangle.zero
    | WalkingArrow.one => WalkingTriangle.two
  map f := match f with
    | WalkingArrowHom.id _ => WalkingTriangleHom.id _
    | morph => middle
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;> {dsimp; simp}

structure FactorizationFunctor where
  func : (WalkingArrow ⥤ C) ⥤ (WalkingTriangle ⥤ C)
  cond : func ⋙ ((whiskeringLeft WalkingArrow WalkingTriangle C).obj MiddleFunctor) = Functor.id (WalkingArrow ⥤ C)

def Unit (FF : FactorizationFunctor) :
