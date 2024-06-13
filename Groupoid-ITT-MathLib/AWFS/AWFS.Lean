import AWFS.TAFunctors

open CategoryTheory
open Diagrams
open WalkingTriangle
open WalkingArrow
open WalkingTriangleHom
open WalkingArrowHom

universe v v₂ u u₂
variable {C : Type u} [Category.{v} C]

structure FactorizationFunctor where
  func : (WalkingArrow ⥤ C) ⥤ (WalkingTriangle ⥤ C)
  cond : func ⋙ PreCompMiddleFunctor = Functor.id (WalkingArrow ⥤ C)

def FF_Unit {FF : @FactorizationFunctor C _} : NatTrans (Functor.id (WalkingArrow ⥤ C)) (FF.func ⋙ PreCompRightFunctor) := by
  rw [<- FF.cond]
  apply NatTrans.hcomp (NatTrans.id FF.func)
  simp [Quiver.Hom]
  exact (@NatTrans_PCMF_PCRF C _)

def FF_CoUnit {FF : @FactorizationFunctor C _} : NatTrans (FF.func ⋙ PreCompLeftFunctor) (Functor.id (WalkingArrow ⥤ C)) := by
  rw [<- FF.cond]
  apply NatTrans.hcomp (NatTrans.id FF.func)
  simp [Quiver.Hom]
  exact (@NatTrans_PCLF_PCMF C _)

structure AWFS extends @FactorizationFunctor C _ where
  multiplication : ((func ⋙ PreCompRightFunctor) ⋙ (func ⋙ PreCompRightFunctor)) ⟶ (func ⋙ PreCompRightFunctor)
  comultiplication : (func ⋙ PreCompLeftFunctor) ⟶ ((func ⋙ PreCompLeftFunctor) ⋙ (func ⋙ PreCompLeftFunctor))
  Right_assoc : (multiplication ◫ (𝟙 (func ⋙ PreCompRightFunctor))) ≫ multiplication = ((𝟙 (func ⋙ PreCompRightFunctor)) ◫ multiplication) ≫ multiplication
  left_unit : (FF_Unit ◫ (𝟙 (func ⋙ PreCompRightFunctor))) ≫ multiplication = (𝟙 (func ⋙ PreCompRightFunctor))
  right_unit : ((𝟙 (func ⋙ PreCompRightFunctor)) ◫ FF_Unit) ≫ multiplication = (𝟙 (func ⋙ PreCompRightFunctor))
  Left_assoc : comultiplication ≫ ((𝟙 (func ⋙ PreCompLeftFunctor)) ◫ comultiplication) = comultiplication ≫ (comultiplication ◫ (𝟙 (func ⋙ PreCompLeftFunctor)))
  left_counit : comultiplication ≫ (FF_CoUnit ◫ (𝟙 (func ⋙ PreCompLeftFunctor))) = (𝟙 (func ⋙ PreCompLeftFunctor))
  right_counit : comultiplication ≫ ((𝟙 (func ⋙ PreCompLeftFunctor)) ◫ FF_CoUnit) = (𝟙 (func ⋙ PreCompLeftFunctor))
