// Generated by js_of_ocaml
//# buildInfo:effects=false, kind=cma, use-js-string=true, version=5.8.1

//# unitInfo: Provides: Javascript_profiling
//# unitInfo: Requires: Expect_test_collector, Ppx_bench_lib__Benchmark_accumulator, Ppx_inline_test_lib__Runtime, Ppx_module_timer_runtime, Stdlib
(function
  (globalThis){
   "use strict";
   var
    runtime = globalThis.jsoo_runtime,
    cst_Javascript_profiling = "Javascript_profiling",
    cst_javascript_profiling = "javascript_profiling";
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
    Stdlib = global_data.Stdlib,
    Ppx_module_timer_runtime = global_data.Ppx_module_timer_runtime,
    Ppx_bench_lib_Benchmark_accumu =
      global_data.Ppx_bench_lib__Benchmark_accumulator,
    Expect_test_collector = global_data.Expect_test_collector,
    Ppx_inline_test_lib_Runtime = global_data.Ppx_inline_test_lib__Runtime;
   caml_call1(Ppx_module_timer_runtime[4], cst_Javascript_profiling);
   caml_call1(Ppx_bench_lib_Benchmark_accumu[1][1], cst_javascript_profiling);
   caml_call1
    (Expect_test_collector[5][1],
     "javascript_profiling/javascript_profiling.ml");
   caml_call2(Ppx_inline_test_lib_Runtime[2], cst_javascript_profiling, cst);
   var cst_before = "_before", cst_after = "_after";
   function mark(name){return runtime.js_prof_mark(name);}
   function measure(name, start, end){
    return runtime.js_prof_measure(name, start, end);
   }
   function record(name, f){
    var
     before_name = caml_call2(Stdlib[28], name, cst_before),
     after_name = caml_call2(Stdlib[28], name, cst_after);
    runtime.js_prof_mark(before_name);
    var res = caml_call1(f, 0);
    runtime.js_prof_mark(after_name);
    runtime.js_prof_measure(name, before_name, after_name);
    return res;
   }
   function clear_marks(param){return runtime.js_prof_clear_marks(0);}
   function clear_measures(param){return runtime.js_prof_clear_measures(0);}
   var Manual = [0, mark, measure];
   caml_call1(Ppx_inline_test_lib_Runtime[3], cst_javascript_profiling);
   caml_call1(Expect_test_collector[5][2], 0);
   caml_call1(Ppx_bench_lib_Benchmark_accumu[1][2], 0);
   caml_call1(Ppx_module_timer_runtime[5], cst_Javascript_profiling);
   var
    Javascript_profiling = [0, record, clear_marks, clear_measures, Manual];
   runtime.caml_register_global
    (14, Javascript_profiling, cst_Javascript_profiling);
   return;
  }
  (globalThis));

//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLjAsImZpbGUiOiJqYXZhc2NyaXB0X3Byb2ZpbGluZy5jbWEuanMiLCJzb3VyY2VSb290IjoiIiwibmFtZXMiOlsibWFyayIsIm5hbWUiLCJtZWFzdXJlIiwic3RhcnQiLCJlbmQiLCJyZWNvcmQiLCJmIiwiYmVmb3JlX25hbWUiLCJhZnRlcl9uYW1lIiwicmVzIiwiY2xlYXJfbWFya3MiLCJjbGVhcl9tZWFzdXJlcyJdLCJzb3VyY2VzIjpbIi9Vc2Vycy9qYWNvYnppZmYvLm9wYW0vZGl5LWhhemVsbnV0L2xpYi9pbmNyX2RvbS9qYXZhc2NyaXB0X3Byb2ZpbGluZy9qYXZhc2NyaXB0X3Byb2ZpbGluZy5tbCJdLCJtYXBwaW5ncyI6Ijs7Ozs7Ozs7Ozs7O0c7Ozs7O0c7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztZQUtJQSxLQUFLQyxNQUFPLE9BQUEscUJBQVBBLE1BQXdCO1lBQzdCQyxRQUFTRCxNQUFNRSxPQUFPQztJQUFPLE9BQUEsd0JBQXBCSCxNQUFNRSxPQUFPQztHQUFzQztZQUU1REMsT0FGU0osTUFFSUs7SUFDZjtLQUpPQyxjQUlXLHVCQUhQTjtLQURKTyxhQUtVLHVCQUpOUDtJQURHLHFCQUFQTTtJQU9HLElBQU5FLE1BQU0sV0FKS0g7SUFIRCxxQkFBUEU7SUFDd0Isd0JBQXBCUCxNQURKTSxhQUFBQztJQVNQLE9BRklDO0dBR0Q7WUFHREMsbUJBQWlCLE9BQUEsK0JBQXNCO1lBQ3ZDQyxzQkFBb0IsT0FBQSxrQ0FBeUI7R0FFakMsaUJBaEJaWCxNQUNBRTs7Ozs7OytCQUVBRyxRQVVBSyxhQUNBQzs7OztFIiwic291cmNlc0NvbnRlbnQiOlsiZXh0ZXJuYWwganNfcHJvZl9tYXJrIDogc3RyaW5nIC0+IHVuaXQgPSBcImpzX3Byb2ZfbWFya1wiXG5leHRlcm5hbCBqc19wcm9mX21lYXN1cmUgOiBzdHJpbmcgLT4gc3RyaW5nIC0+IHN0cmluZyAtPiB1bml0ID0gXCJqc19wcm9mX21lYXN1cmVcIlxuZXh0ZXJuYWwganNfcHJvZl9jbGVhcl9tYXJrcyA6IHVuaXQgLT4gdW5pdCA9IFwianNfcHJvZl9jbGVhcl9tYXJrc1wiXG5leHRlcm5hbCBqc19wcm9mX2NsZWFyX21lYXN1cmVzIDogdW5pdCAtPiB1bml0ID0gXCJqc19wcm9mX2NsZWFyX21lYXN1cmVzXCJcblxubGV0IG1hcmsgbmFtZSA9IGpzX3Byb2ZfbWFyayBuYW1lXG5sZXQgbWVhc3VyZSB+bmFtZSB+c3RhcnQgfmVuZF8gPSBqc19wcm9mX21lYXN1cmUgbmFtZSBzdGFydCBlbmRfXG5cbmxldCByZWNvcmQgbmFtZSB+ZiA9XG4gIGxldCBiZWZvcmVfbmFtZSA9IG5hbWUgXiBcIl9iZWZvcmVcIiBpblxuICBsZXQgYWZ0ZXJfbmFtZSA9IG5hbWUgXiBcIl9hZnRlclwiIGluXG4gIGxldCAoKSA9IG1hcmsgYmVmb3JlX25hbWUgaW5cbiAgbGV0IHJlcyA9IGYgKCkgaW5cbiAgbGV0ICgpID0gbWFyayBhZnRlcl9uYW1lIGluXG4gIG1lYXN1cmUgfm5hbWUgfnN0YXJ0OmJlZm9yZV9uYW1lIH5lbmRfOmFmdGVyX25hbWU7XG4gIHJlc1xuOztcblxubGV0IGNsZWFyX21hcmtzICgpID0ganNfcHJvZl9jbGVhcl9tYXJrcyAoKVxubGV0IGNsZWFyX21lYXN1cmVzICgpID0ganNfcHJvZl9jbGVhcl9tZWFzdXJlcyAoKVxuXG5tb2R1bGUgTWFudWFsID0gc3RydWN0XG4gIGxldCBtYXJrID0gbWFya1xuICBsZXQgbWVhc3VyZSA9IG1lYXN1cmVcbmVuZFxuIl19
