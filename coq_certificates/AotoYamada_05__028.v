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
| TconsIF  
| Tfalse  
| Tfilter  
| Tnil  
| Ttrue.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tcons  =>  a ⟶ c ⟶ c
  | TconsIF  =>  b ⟶ a ⟶ c ⟶ c
  | Tfalse  =>  b
  | Tfilter  =>  (a ⟶ b) ⟶ c ⟶ c
  | Tnil  =>  c
  | Ttrue => b
end.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition consIF {C} : tm fn_arity C _ := 
BaseTm TconsIF.
Definition false {C} : tm fn_arity C _ := 
BaseTm Tfalse.
Definition filter {C} : tm fn_arity C _ := 
BaseTm Tfilter.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition true {C} : tm fn_arity C _ := 
BaseTm Ttrue.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (consIF · true ·  V 0 ·  V 1)
    (cons ·  V 0 ·  V 1).
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (consIF · false ·  V 0 ·  V 1)
     V 1.
Program Definition rule_2 := 
    make_rewrite
    (_ ,, ∙) _
    (filter ·  V 0 · nil)
    nil.
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter ·  V 0 · (cons ·  V 1 ·  V 2))
    (consIF · ( V 0 ·  V 1) ·  V 1 · (filter ·  V 0 ·  V 2)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 2 + P_const 2 * y0 + P_const 2 * y1 + P_const 3 * y0 * y1))
| TconsIF  => 
 λP
λP let y1 := P_var (Vs Vz) in
λP let y2 := P_var Vz in
(to_Poly (P_const 2 * y1 + P_const 2 * y2 + P_const 3 * y1 * y2))
| Tfalse  => 
 (to_Poly (P_const 3))
| Tfilter  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 * y1 + P_const 2 * y1 * (G0 ·P (y1))))
| Tnil  => 
 (to_Poly (P_const 3))
| Ttrue => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
