Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Ca  
| Cb  
| Cc.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition a := 
Base Ca.
Definition b := 
Base Cb.
Definition c := 
Base Cc.



Inductive fun_symbols := 
| Tcons  
| TdropWhile  
| TIF  
| Tnil  
| TtakeWhile  
| Ttrue.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tcons  =>  a ⟶ c ⟶ c
  | TdropWhile  =>  (a ⟶ b) ⟶ c ⟶ c
  | TIF  =>  b ⟶ c ⟶ c ⟶ c
  | Tnil  =>  c
  | TtakeWhile  =>  (a ⟶ b) ⟶ c ⟶ c
  | Ttrue => b
end.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition dropWhile {C} : tm fn_arity C _ := 
BaseTm TdropWhile.
Definition IF {C} : tm fn_arity C _ := 
BaseTm TIF.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition takeWhile {C} : tm fn_arity C _ := 
BaseTm TtakeWhile.
Definition true {C} : tm fn_arity C _ := 
BaseTm Ttrue.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (IF · true ·  V 0 ·  V 1)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (IF · true ·  V 0 ·  V 1)
     V 1.
Program Definition rule_2 := 
    make_rewrite
    (_ ,, ∙) _
    (takeWhile ·  V 0 · nil)
    nil.
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (takeWhile ·  V 0 · (cons ·  V 1 ·  V 2))
    (IF · ( V 0 ·  V 1) · (cons ·  V 1 · (takeWhile ·  V 0 ·  V 2)) · nil).
Program Definition rule_4 := 
    make_rewrite
    (_ ,, ∙) _
    (dropWhile ·  V 0 · nil)
    nil.
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (dropWhile ·  V 0 · (cons ·  V 1 ·  V 2))
    (IF · ( V 0 ·  V 1) · (dropWhile ·  V 0 ·  V 2) · (cons ·  V 1 ·  V 2)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_0 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 2 + P_const 2 * y0 * y1 + P_const 3 * y0 + P_const 3 * y1))
| TdropWhile  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y1 + P_const 2 * y1 * (G0 ·P (y1))))
| TIF  => 
 λP
λP
λP
(to_Poly (P_const 0))
| Tnil  => 
 (to_Poly (P_const 1))
| TtakeWhile  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 2 * y1 + P_const 3 * y1 * (G0 ·P (y1))))
| Ttrue => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
