// Generated by js_of_ocaml
//# buildInfo:effects=false, kind=cma, use-js-string=true, version=5.8.1

//# unitInfo: Provides: Uopt
//# unitInfo: Requires: Core, Expect_test_collector, Ppx_bench_lib__Benchmark_accumulator, Ppx_inline_test_lib__Runtime, Ppx_module_timer_runtime
(function
  (globalThis){
   "use strict";
   var
    runtime = globalThis.jsoo_runtime,
    cst_Uopt = "Uopt",
    cst_uopt = "uopt";
   function caml_call1(f, a0){
    return (f.l >= 0 ? f.l : f.l = f.length) == 1
            ? f(a0)
            : runtime.caml_call_gen(f, [a0]);
   }
   function caml_call2(f, a0, a1){
    return (f.l >= 0 ? f.l : f.l = f.length) == 2
            ? f(a0, a1)
            : runtime.caml_call_gen(f, [a0, a1]);
   }
   var
    global_data = runtime.caml_get_global_data(),
    cst = "",
    none = "Uopt.none",
    Core = global_data.Core,
    Ppx_module_timer_runtime = global_data.Ppx_module_timer_runtime,
    Ppx_bench_lib_Benchmark_accumu =
      global_data.Ppx_bench_lib__Benchmark_accumulator,
    Expect_test_collector = global_data.Expect_test_collector,
    Ppx_inline_test_lib_Runtime = global_data.Ppx_inline_test_lib__Runtime;
   caml_call1(Ppx_module_timer_runtime[4], cst_Uopt);
   caml_call1(Ppx_bench_lib_Benchmark_accumu[1][1], cst_uopt);
   caml_call1(Expect_test_collector[5][1], "uopt/src/uopt.ml");
   caml_call2(Ppx_inline_test_lib_Runtime[2], cst_uopt, cst);
   var
    _a_ = [0, "None"],
    _b_ = [0, "Some"],
    cst_Uopt_value_exn = "Uopt.value_exn";
   function some(x){return x;}
   function unsafe_value(x){return x;}
   function is_none(t){return caml_call2(Core[246], t, none);}
   function is_some(t){return 1 - is_none(t);}
   function invariant(invariant_a, t){
    var _c_ = is_some(t);
    return _c_ ? caml_call1(invariant_a, t) : _c_;
   }
   function sexp_of_t(sexp_of_a, t){
    return is_none(t) ? _a_ : [1, [0, _b_, [0, caml_call1(sexp_of_a, t), 0]]];
   }
   function value_exn(t){
    return is_none(t) ? caml_call1(Core[6], cst_Uopt_value_exn) : t;
   }
   function to_option(t){return is_none(t) ? 0 : [0, t];}
   function of_option(param){
    if(! param) return none;
    var a = param[1];
    return a;
   }
   var
    Optional_syntax = [0, is_none, unsafe_value],
    Optional_syntax$0 = [0, Optional_syntax];
   caml_call1(Ppx_inline_test_lib_Runtime[3], cst_uopt);
   caml_call1(Expect_test_collector[5][2], 0);
   caml_call1(Ppx_bench_lib_Benchmark_accumu[1][2], 0);
   caml_call1(Ppx_module_timer_runtime[5], cst_Uopt);
   var
    Uopt =
      [0,
       sexp_of_t,
       invariant,
       none,
       some,
       is_none,
       is_some,
       value_exn,
       unsafe_value,
       to_option,
       of_option,
       Optional_syntax$0];
   runtime.caml_register_global(16, Uopt, cst_Uopt);
   return;
  }
  (globalThis));

//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLjAsImZpbGUiOiJ1b3B0LmNtYS5qcyIsInNvdXJjZVJvb3QiOiIiLCJuYW1lcyI6WyJub25lIiwic29tZSIsIngiLCJ1bnNhZmVfdmFsdWUiLCJpc19ub25lIiwidCIsImlzX3NvbWUiLCJpbnZhcmlhbnQiLCJpbnZhcmlhbnRfYSIsInNleHBfb2ZfdCIsInNleHBfb2ZfYSIsInZhbHVlX2V4biIsInRvX29wdGlvbiIsIm9mX29wdGlvbiIsImEiXSwic291cmNlcyI6WyIvVXNlcnMvamFjb2J6aWZmLy5vcGFtL2RpeS1oYXplbG51dC9saWIvY29yZV9rZXJuZWwvdW9wdC91b3B0Lm1sIl0sIm1hcHBpbmdzIjoiOzs7Ozs7Ozs7Ozs7Rzs7Ozs7Rzs7Ozs7Ozs7SUFPSUE7Ozs7Ozs7Ozs7Ozs7OztZQUNBQyxLQUFNQyxHQUFpQixPQUFqQkEsRUFBNEI7WUFDbENDLGFBQWNELEdBQWlCLE9BQWpCQSxFQUE0QjtZQUMxQ0UsUUFBUUMsR0FBSSw2QkFBSkEsR0FIUkwsTUFHNkI7WUFDN0JNLFFBQVFELEdBQUksV0FEWkQsUUFDUUMsR0FBbUI7WUFDM0JFLFVBQVVDLGFBSElIO0lBR2UsVUFEN0JDLFFBRmNEO0lBR2UsYUFBMkIsV0FBOUNHLGFBSElIO0dBRzBEO1lBRXhFSSxVQUFVQyxXQUxJTDtJQU1oQixPQUxFRCxRQURjQyx1Q0FLSkssV0FMSUw7R0FNcUQ7WUFHbkVNLFVBVGNOO0lBU0EsT0FSZEQsUUFEY0MsS0FTa0IsMENBVGxCQTtHQVMrRDtZQUM3RU8sVUFWY1AsR0FVQSxPQVRkRCxRQURjQyxhQUFBQSxHQVVpRDtZQUUvRFE7SUFBWSxtQkFkWmI7UUFDTWM7SUFBaUIsT0FBakJBO0dBZVU7R0FJTztJQUFBLHNCQWpCdkJWLFNBREFEO0lBaUJxQjs7Ozs7Ozs7T0FackJNO09BRkFGO09BTEFQO09BQ0FDO09BRUFHO09BQ0FFO09BT0FLO09BVEFSO09BVUFTO09BRUFDOzs7O0UiLCJzb3VyY2VzQ29udGVudCI6WyJvcGVuIENvcmVcblxudHlwZSArJ2EgdFxuXG4oKiBUaGlzIFtPYmoubWFnaWNdIGlzIE9LIGJlY2F1c2Ugd2UgbmV2ZXIgYWxsb3cgdXNlciBjb2RlIGFjY2VzcyB0byBbbm9uZV0gKGV4Y2VwdCB2aWFcbiAgIFt1bnNhZmVfdmFsdWVdKS4gIFdlIGRpc2FsbG93IFtfIFVvcHQudCBVb3B0LnRdLCBzbyB0aGVyZSBpcyBubyBjaGFuY2Ugb2YgY29uZnVzaW5nXG4gICBbbm9uZV0gd2l0aCBbc29tZSBub25lXS4gIEFuZCBbZmxvYXQgVW9wdC50IGFycmF5XSBpcyBzaW1pbGFybHkgZGlzYWxsb3dlZC4gKilcbmxldCBub25lIDogJ2EgdCA9IE9iai5tYWdpYyBcIlVvcHQubm9uZVwiXG5sZXQgc29tZSAoeCA6ICdhKSA6ICdhIHQgPSBPYmoubWFnaWMgeFxubGV0IHVuc2FmZV92YWx1ZSAoeCA6ICdhIHQpIDogJ2EgPSBPYmoubWFnaWMgeFxubGV0IGlzX25vbmUgdCA9IHBoeXNfZXF1YWwgdCBub25lXG5sZXQgaXNfc29tZSB0ID0gbm90IChpc19ub25lIHQpXG5sZXQgaW52YXJpYW50IGludmFyaWFudF9hIHQgPSBpZiBpc19zb21lIHQgdGhlbiBpbnZhcmlhbnRfYSAodW5zYWZlX3ZhbHVlIHQpXG5cbmxldCBzZXhwX29mX3Qgc2V4cF9vZl9hIHQgPVxuICBpZiBpc19ub25lIHQgdGhlbiBbJXNleHAgTm9uZV0gZWxzZSBbJXNleHAgU29tZSAodW5zYWZlX3ZhbHVlIHQgOiBhKV1cbjs7XG5cbmxldCB2YWx1ZV9leG4gdCA9IGlmIGlzX25vbmUgdCB0aGVuIGZhaWx3aXRoIFwiVW9wdC52YWx1ZV9leG5cIiBlbHNlIHVuc2FmZV92YWx1ZSB0XG5sZXQgdG9fb3B0aW9uIHQgPSBpZiBpc19ub25lIHQgdGhlbiBOb25lIGVsc2UgU29tZSAodW5zYWZlX3ZhbHVlIHQpXG5cbmxldCBvZl9vcHRpb24gPSBmdW5jdGlvblxuICB8IE5vbmUgLT4gbm9uZVxuICB8IFNvbWUgYSAtPiBzb21lIGFcbjs7XG5cbm1vZHVsZSBPcHRpb25hbF9zeW50YXggPSBzdHJ1Y3RcbiAgbW9kdWxlIE9wdGlvbmFsX3N5bnRheCA9IHN0cnVjdFxuICAgIGxldCBpc19ub25lID0gaXNfbm9uZVxuICAgIGxldCB1bnNhZmVfdmFsdWUgPSB1bnNhZmVfdmFsdWVcbiAgZW5kXG5lbmRcbiJdfQ==
