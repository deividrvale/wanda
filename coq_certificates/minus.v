Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| CN.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition N := 
Base CN.



Inductive fun_symbols := 
| TmINus  
| Ts  
| Tz.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | TmINus  =>  N ⟶ N ⟶ N
  | Ts  =>  N ⟶ N
  | Tz => N
end.
Definition mINus {C} : tm fn_arity C _ := 
BaseTm TmINus.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition z {C} : tm fn_arity C _ := 
BaseTm Tz.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (mINus · z ·  V 0)
    z.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, ∙) _
    (mINus ·  V 0 · z)
     V 0.
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (mINus · (s ·  V 0) · (s ·  V 1))
    (mINus ·  V 0 ·  V 1).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, ∙) _
    (mINus ·  V 0 ·  V 0)
    z.

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| TmINus  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Ts  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Tz => 
(to_Poly (P_const 2))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
