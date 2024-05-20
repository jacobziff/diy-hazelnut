// Generated by js_of_ocaml
//# buildInfo:effects=false, kind=cma, use-js-string=true, version=5.8.1

//# unitInfo: Provides: Thread_safe_queue__
(function
  (globalThis){
   "use strict";
   var runtime = globalThis.jsoo_runtime, Thread_safe_queue = [0];
   runtime.caml_register_global(0, Thread_safe_queue, "Thread_safe_queue__");
   return;
  }
  (globalThis));

//# unitInfo: Provides: Thread_safe_queue__Import
//# unitInfo: Requires: Expect_test_collector, Ppx_bench_lib__Benchmark_accumulator, Ppx_inline_test_lib__Runtime, Ppx_module_timer_runtime
(function
  (globalThis){
   "use strict";
   var
    runtime = globalThis.jsoo_runtime,
    cst_Thread_safe_queue_Import = "Thread_safe_queue__Import",
    cst_thread_safe_queue = "thread_safe_queue";
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
    Ppx_module_timer_runtime = global_data.Ppx_module_timer_runtime,
    Ppx_bench_lib_Benchmark_accumu =
      global_data.Ppx_bench_lib__Benchmark_accumulator,
    Expect_test_collector = global_data.Expect_test_collector,
    Ppx_inline_test_lib_Runtime = global_data.Ppx_inline_test_lib__Runtime;
   caml_call1(Ppx_module_timer_runtime[4], cst_Thread_safe_queue_Import);
   caml_call1(Ppx_bench_lib_Benchmark_accumu[1][1], cst_thread_safe_queue);
   caml_call1(Expect_test_collector[5][1], "thread_safe_queue/src/import.ml");
   caml_call2(Ppx_inline_test_lib_Runtime[2], cst_thread_safe_queue, cst);
   caml_call1(Ppx_inline_test_lib_Runtime[3], cst_thread_safe_queue);
   caml_call1(Expect_test_collector[5][2], 0);
   caml_call1(Ppx_bench_lib_Benchmark_accumu[1][2], 0);
   caml_call1(Ppx_module_timer_runtime[5], cst_Thread_safe_queue_Import);
   var Thread_safe_queue_Import = [0];
   runtime.caml_register_global
    (11, Thread_safe_queue_Import, cst_Thread_safe_queue_Import);
   return;
  }
  (globalThis));

//# unitInfo: Provides: Thread_safe_queue
//# unitInfo: Requires: Assert_failure, Base__Field, Base__Invariant, Core, Expect_test_collector, Ppx_bench_lib__Benchmark_accumulator, Ppx_inline_test_lib__Runtime, Ppx_module_timer_runtime, Sexplib0__Sexp_conv, Uopt
(function
  (globalThis){
   "use strict";
   var
    runtime = globalThis.jsoo_runtime,
    cst_Thread_safe_queue = "Thread_safe_queue",
    cst$0 = "_",
    cst_back = "back",
    cst_front = "front",
    cst_length = "length",
    cst_thread_safe_queue = "thread_safe_queue",
    cst_thread_safe_queue_src_thre =
      "thread_safe_queue/src/thread_safe_queue.ml",
    cst_unused_elts = "unused_elts",
    caml_maybe_attach_backtrace = runtime.caml_maybe_attach_backtrace;
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
   function caml_call4(f, a0, a1, a2, a3){
    return (f.l >= 0 ? f.l : f.l = f.length) == 4
            ? f(a0, a1, a2, a3)
            : runtime.caml_call_gen(f, [a0, a1, a2, a3]);
   }
   function caml_call5(f, a0, a1, a2, a3, a4){
    return (f.l >= 0 ? f.l : f.l = f.length) == 5
            ? f(a0, a1, a2, a3, a4)
            : runtime.caml_call_gen(f, [a0, a1, a2, a3, a4]);
   }
   var
    global_data = runtime.caml_get_global_data(),
    cst = "",
    Uopt = global_data.Uopt,
    Core = global_data.Core,
    Assert_failure = global_data.Assert_failure,
    Base_Invariant = global_data.Base__Invariant;
   global_data.Base__Field;
   var
    Sexplib0_Sexp_conv = global_data.Sexplib0__Sexp_conv,
    Ppx_module_timer_runtime = global_data.Ppx_module_timer_runtime,
    Ppx_bench_lib_Benchmark_accumu =
      global_data.Ppx_bench_lib__Benchmark_accumulator,
    Expect_test_collector = global_data.Expect_test_collector,
    Ppx_inline_test_lib_Runtime = global_data.Ppx_inline_test_lib__Runtime;
   caml_call1(Ppx_module_timer_runtime[4], cst_Thread_safe_queue);
   caml_call1(Ppx_bench_lib_Benchmark_accumu[1][1], cst_thread_safe_queue);
   caml_call1(Expect_test_collector[5][1], cst_thread_safe_queue_src_thre);
   caml_call2(Ppx_inline_test_lib_Runtime[2], cst_thread_safe_queue, cst);
   var _a_ = [0, "next"], _b_ = [0, "value"];
   function sexp_of_t(of_a_001, param){
    var
     value_003 = param[1],
     next_005 = param[2],
     arg_006 = caml_call1(Sexplib0_Sexp_conv[23], next_005),
     bnds_002 = [0, [1, [0, _a_, [0, arg_006, 0]]], 0],
     arg_004 = caml_call2(Uopt[1], of_a_001, value_003),
     bnds_002$0 = [0, [1, [0, _b_, [0, arg_004, 0]]], bnds_002];
    return [1, bnds_002$0];
   }
   function create(param){return [0, Uopt[3], Uopt[3]];}
   function unused_elts(r){return r[4];}
   function set_unused_elts(r, v){r[4] = v; return 0;}
   function back(r){return r[3];}
   function set_back(r, v){r[3] = v; return 0;}
   function front(r){return r[2];}
   function set_front(r, v){r[2] = v; return 0;}
   function length(r){return r[1];}
   function set_length(r, v){r[1] = v; return 0;}
   var
    unused_elts$0 =
      [0,
       function(param){return 0;},
       cst_unused_elts,
       [0, set_unused_elts],
       unused_elts,
       function(r, v){return [0, r[1], r[2], r[3], v];}],
    back$0 =
      [0,
       function(param){return 0;},
       cst_back,
       [0, set_back],
       back,
       function(r, v){return [0, r[1], r[2], v, r[4]];}],
    front$0 =
      [0,
       function(param){return 0;},
       cst_front,
       [0, set_front],
       front,
       function(r, v){return [0, r[1], v, r[3], r[4]];}],
    length$0 =
      [0,
       function(param){return 0;},
       cst_length,
       [0, set_length],
       length,
       function(r, v){return [0, v, r[2], r[3], r[4]];}],
    _c_ = [0, cst_unused_elts],
    _d_ = [0, cst_back],
    _e_ = [0, cst_front],
    _f_ = [0, cst_length],
    _g_ = [0, cst_thread_safe_queue_src_thre, 62, 13],
    _h_ = [0, cst_thread_safe_queue_src_thre, 55, 32],
    _i_ = [0, cst_thread_safe_queue_src_thre, 52, 13],
    _j_ = [0, cst_thread_safe_queue_src_thre, 54, 11],
    _k_ = [0, cst_thread_safe_queue_src_thre, 43, 36],
    _l_ = [0, cst$0],
    _m_ = [0, cst_thread_safe_queue_src_thre, 40, 1533, 1555],
    _n_ = [0, cst$0],
    cst_Thread_safe_queue_dequeue_ =
      "Thread_safe_queue.dequeue_exn of empty queue",
    _o_ = [0, cst_thread_safe_queue_src_thre, 102, 3230, 3248];
   function sexp_of_t$0(of_a_007, param){
    var
     length_009 = param[1],
     front_011 = param[2],
     back_013 = param[3],
     unused_elts_015 = param[4],
     arg_016 =
       caml_call2
        (Uopt[1],
         function(_r_){return sexp_of_t(of_a_007, _r_);},
         unused_elts_015),
     bnds_008 = [0, [1, [0, _c_, [0, arg_016, 0]]], 0],
     arg_014 = sexp_of_t(of_a_007, back_013),
     bnds_008$0 = [0, [1, [0, _d_, [0, arg_014, 0]]], bnds_008],
     arg_012 = sexp_of_t(of_a_007, front_011),
     bnds_008$1 = [0, [1, [0, _e_, [0, arg_012, 0]]], bnds_008$0],
     arg_010 = caml_call1(Core[356], length_009),
     bnds_008$2 = [0, [1, [0, _f_, [0, arg_010, 0]]], bnds_008$1];
    return [1, bnds_008$2];
   }
   function invariant(invariant_a, t){
    return caml_call4
            (Base_Invariant[1],
             _m_,
             t,
             function(x_017){
              return sexp_of_t$0(function(param){return _l_;}, x_017);
             },
             function(param){
              function check(f){return caml_call2(Base_Invariant[2], t, f);}
              var
               unused_elts_fun =
                 check
                  (function(unused_elts){
                    var r = [0, unused_elts];
                    for(;;){
                     if(! caml_call1(Uopt[6], r[1])) return 0;
                     var elt = caml_call1(Uopt[7], r[1]);
                     r[1] = elt[2];
                     if(! caml_call1(Uopt[5], elt[1]))
                      throw caml_maybe_attach_backtrace
                             ([0, Assert_failure, _g_], 1);
                    }
                   }),
               back_fun =
                 check
                  (function(back){
                    if(caml_call1(Uopt[5], back[1])) return 0;
                    throw caml_maybe_attach_backtrace
                           ([0, Assert_failure, _h_], 1);
                   }),
               front_fun =
                 check
                  (function(front){
                    var i = [0, t[1]], r = [0, front];
                    for(;;){
                     if(! caml_call2(Core[91], i[1], 0)){
                      if(caml_call2(Core[246], r[1], t[3])) return 0;
                      throw caml_maybe_attach_backtrace
                             ([0, Assert_failure, _j_], 1);
                     }
                     i[1]--;
                     var elt = r[1];
                     r[1] = caml_call1(Uopt[7], elt[2]);
                     if(! caml_call1(Uopt[6], elt[1]))
                      throw caml_maybe_attach_backtrace
                             ([0, Assert_failure, _i_], 1);
                    }
                   }),
               length_fun =
                 check
                  (function(length){
                    if(caml_call2(Core[88], length, 0)) return 0;
                    throw caml_maybe_attach_backtrace
                           ([0, Assert_failure, _k_], 1);
                   });
              caml_call1(length_fun, length$0);
              caml_call1(front_fun, front$0);
              caml_call1(back_fun, back$0);
              return caml_call1(unused_elts_fun, unused_elts$0);
             });
   }
   function create$0(param){
    var elt = create(0);
    return [0, 0, elt, elt, Uopt[3]];
   }
   function enqueue(t, a){
    if(caml_call1(Uopt[6], t[4])){
     var elt = caml_call1(Uopt[8], t[4]);
     t[4] = elt[2];
     var new_back = elt;
    }
    else
     var new_back = create(0);
    t[1] = t[1] + 1 | 0;
    var _p_ = caml_call1(Uopt[4], a);
    t[3][1] = _p_;
    var _q_ = caml_call1(Uopt[4], new_back);
    t[3][2] = _q_;
    t[3] = new_back;
    return 0;
   }
   function dequeue_exn(t){
    if(caml_call2(Core[90], t[1], 0))
     caml_call5
      (Core[236],
       0,
       _o_,
       cst_Thread_safe_queue_dequeue_,
       t,
       function(x_018){
        return sexp_of_t$0(function(param){return _n_;}, x_018);
       });
    var elt = t[2], a = elt[1];
    t[2] = caml_call1(Uopt[8], elt[2]);
    t[1] = t[1] - 1 | 0;
    elt[1] = Uopt[3];
    elt[2] = t[4];
    t[4] = caml_call1(Uopt[4], elt);
    return caml_call1(Uopt[8], a);
   }
   function clear_internal_pool(t){t[4] = Uopt[3]; return 0;}
   caml_call1(Ppx_inline_test_lib_Runtime[3], cst_thread_safe_queue);
   caml_call1(Expect_test_collector[5][2], 0);
   caml_call1(Ppx_bench_lib_Benchmark_accumu[1][2], 0);
   caml_call1(Ppx_module_timer_runtime[5], cst_Thread_safe_queue);
   var
    Thread_safe_queue =
      [0,
       sexp_of_t$0,
       invariant,
       create$0,
       length,
       enqueue,
       dequeue_exn,
       clear_internal_pool,
       [0, [0, Uopt[1], Uopt[3], Uopt[4], Uopt[5], Uopt[6]]]];
   runtime.caml_register_global(38, Thread_safe_queue, cst_Thread_safe_queue);
   return;
  }
  (globalThis));

//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLjAsImZpbGUiOiJ0aHJlYWRfc2FmZV9xdWV1ZS5jbWEuanMiLCJzb3VyY2VSb290IjoiIiwibmFtZXMiOlsic2V4cF9vZl90Iiwib2ZfYV8wMDEiLCJ2YWx1ZV8wMDMiLCJuZXh0XzAwNSIsImFyZ18wMDYiLCJibmRzXzAwMiIsImFyZ18wMDQiLCJibmRzXzAwMiQwIiwiY3JlYXRlIiwidW51c2VkX2VsdHMiLCJyIiwic2V0X3VudXNlZF9lbHRzIiwidiIsImJhY2siLCJzZXRfYmFjayIsImZyb250Iiwic2V0X2Zyb250IiwibGVuZ3RoIiwic2V0X2xlbmd0aCIsInVudXNlZF9lbHRzJDAiLCJiYWNrJDAiLCJmcm9udCQwIiwibGVuZ3RoJDAiLCJzZXhwX29mX3QkMCIsIm9mX2FfMDA3IiwibGVuZ3RoXzAwOSIsImZyb250XzAxMSIsImJhY2tfMDEzIiwidW51c2VkX2VsdHNfMDE1IiwiYXJnXzAxNiIsImJuZHNfMDA4IiwiYXJnXzAxNCIsImJuZHNfMDA4JDAiLCJhcmdfMDEyIiwiYm5kc18wMDgkMSIsImFyZ18wMTAiLCJibmRzXzAwOCQyIiwiaW52YXJpYW50IiwiaW52YXJpYW50X2EiLCJ0IiwieF8wMTciLCJjaGVjayIsImYiLCJ1bnVzZWRfZWx0c19mdW4iLCJlbHQiLCJiYWNrX2Z1biIsImZyb250X2Z1biIsImkiLCJsZW5ndGhfZnVuIiwiY3JlYXRlJDAiLCJlbnF1ZXVlIiwiYSIsIm5ld19iYWNrIiwiZGVxdWV1ZV9leG4iLCJ4XzAxOCIsImNsZWFyX2ludGVybmFsX3Bvb2wiXSwic291cmNlcyI6WyIvVXNlcnMvamFjb2J6aWZmLy5vcGFtL2RpeS1oYXplbG51dC9saWIvY29yZV9rZXJuZWwvdGhyZWFkX3NhZmVfcXVldWUvdGhyZWFkX3NhZmVfcXVldWUubWwiXSwibWFwcGluZ3MiOiI7Ozs7Ozs7Ozs7RTs7Ozs7Ozs7Ozs7O0c7Ozs7O0c7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7RTs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Rzs7Ozs7Rzs7Ozs7Rzs7Ozs7Rzs7Ozs7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U0FPRlEsV0ExREE1QztJQXlEZ0IrQixPQUFBQTtJQUlKLFVBQUEsb0JBSmNZO0lBQVZaO0lBS0wsVUFBQSxvQkFKWGE7SUFEZ0JiO0lBQUFBLE9BQ2hCYTs7R0FLYztZQWtCaEJDLFlBQVlkO0lBRWQsR0FBRyxxQkFGV0E7Ozs7OztPQUFBQTtnQkFIc0VlO1EsT0EzRXRGL0IsNEIsY0EyRXNGK0I7O0lBT3BGLElBakJ1QlYsTUFhVEwsTUFJVlksSUFqQm1CUDtJQWFUTCxPQUtILG9CQWxCWUs7SUFhVEwsT0FBQUE7SUFiU0s7SUFBQUEsU0FhVEw7SUFBQUEsT0FURyxvQkFKTUs7SUFxQnZCLE9BQUEsb0JBSklPO0dBS2U7WUFHakJJLG9CQUFvQmhCLEdBQUFBLHlCQUE4Qjs7Ozs7Ozs7T0ExRnREaEI7T0FZSWM7T0EyQkFZO09BdENRaEM7T0FxRFJpQztPQXdCQUc7T0FZQUU7Ozs7RSIsInNvdXJjZXNDb250ZW50IjpbIigqIFRoaXMgbW9kdWxlIGV4cGxvaXRzIHRoZSBmYWN0IHRoYXQgT0NhbWwgZG9lcyBub3QgcGVyZm9ybSBjb250ZXh0LXN3aXRjaGVzIHVuZGVyXG4gICBjZXJ0YWluIGNvbmRpdGlvbnMuICBJdCBjYW4gdGhlcmVmb3JlIGF2b2lkIHVzaW5nIG11dGV4ZXMuXG5cbiAgIEdpdmVuIHRoZSBzZW1hbnRpY3Mgb2YgdGhlIGN1cnJlbnQgT0NhbWwgcnVudGltZSAoYW5kIGZvciB0aGUgZm9yZXNlZWFibGUgZnV0dXJlKSwgY29kZVxuICAgc2VjdGlvbnMgZG9jdW1lbnRlZCBhcyBhdG9taWMgYmVsb3cgd2lsbCBuZXZlciBjb250YWluIGEgY29udGV4dC1zd2l0Y2guICBUaGUgZGVjaWRpbmdcbiAgIGNyaXRlcmlvbiBpcyB3aGV0aGVyIHRoZXkgY29udGFpbiBhbGxvY2F0aW9ucyBvciBjYWxscyB0byBleHRlcm5hbC9idWlsdGluIGZ1bmN0aW9ucy5cbiAgIElmIHRoZXJlIGlzIG5vbmUsIGEgY29udGV4dC1zd2l0Y2ggY2Fubm90IGhhcHBlbi4gIEFzc2lnbm1lbnRzIHdpdGhvdXQgYWxsb2NhdGlvbnMsXG4gICBmaWVsZCBhY2Nlc3MsIHBhdHRlcm4tbWF0Y2hpbmcsIGV0Yy4sIGRvIG5vdCB0cmlnZ2VyIGNvbnRleHQtc3dpdGNoZXMuXG5cbiAgIENvZGUgcmV2aWV3ZXJzIHNob3VsZCB0aGVyZWZvcmUgbWFrZSBzdXJlIHRoYXQgdGhlIHNlY3Rpb25zIGRvY3VtZW50ZWQgYXMgYXRvbWljIGJlbG93XG4gICBkbyBub3QgdmlvbGF0ZSB0aGUgYWJvdmUgYXNzdW1wdGlvbnMuICBJdCBpcyBwcnVkZW50IHRvIGRpc2Fzc2VtYmxlIHRoZSAubyBmaWxlICh1c2luZ1xuICAgW29iamR1bXAgLWRyXSkgYW5kIGV4YW1pbmUgaXQuICopXG5cbm9wZW4hIENvcmVcbm9wZW4hIEltcG9ydFxuXG5tb2R1bGUgRWx0ID0gc3RydWN0XG4gIHR5cGUgJ2EgdCA9XG4gICAgeyBtdXRhYmxlIHZhbHVlIDogJ2EgVW9wdC50XG4gICAgOyBtdXRhYmxlIG5leHQgOiAoJ2EgdCBVb3B0LnRbQHNleHAub3BhcXVlXSlcbiAgICB9XG4gIFtAQGRlcml2aW5nIHNleHBfb2ZdXG5cbiAgbGV0IGNyZWF0ZSAoKSA9IHsgdmFsdWUgPSBVb3B0Lm5vbmU7IG5leHQgPSBVb3B0Lm5vbmUgfVxuZW5kXG5cbnR5cGUgJ2EgdCA9XG4gIHsgbXV0YWJsZSBsZW5ndGggOiBpbnRcbiAgKCogW2Zyb250XSB0byBbYmFja10gaGFzIFtsZW5ndGggKyAxXSBsaW5rZWQgZWxlbWVudHMsIHdoZXJlIHRoZSBmaXJzdCBbbGVuZ3RoXSBob2xkIHRoZVxuICAgICB2YWx1ZXMgaW4gdGhlIHF1ZXVlLCBhbmQgdGhlIGxhc3QgaXMgW2JhY2tdLCBob2xkaW5nIG5vIHZhbHVlLiAqKVxuICA7IG11dGFibGUgZnJvbnQgOiAnYSBFbHQudFxuICA7IG11dGFibGUgYmFjayA6ICdhIEVsdC50XG4gICgqIFt1bnVzZWRfZWx0c10gaXMgc2luZ2x5IGxpbmtlZCB2aWEgW25leHRdLCBhbmQgZW5kcyB3aXRoIFtzZW50aW5lbF0uICBBbGwgZWx0cyBpblxuICAgICBbdW51c2VkX2VsdHNdIGhhdmUgW1VvcHQuaXNfbm9uZSBlbHQudmFsdWVdLiAqKVxuICA7IG11dGFibGUgdW51c2VkX2VsdHMgOiAnYSBFbHQudCBVb3B0LnRcbiAgfVxuW0BAZGVyaXZpbmcgZmllbGRzLCBzZXhwX29mXVxuXG5sZXQgaW52YXJpYW50IF9pbnZhcmlhbnRfYSB0ID1cbiAgSW52YXJpYW50LmludmFyaWFudCBbJWhlcmVdIHQgWyVzZXhwX29mOiBfIHRdIChmdW4gKCkgLT5cbiAgICBsZXQgY2hlY2sgZiA9IEludmFyaWFudC5jaGVja19maWVsZCB0IGYgaW5cbiAgICBGaWVsZHMuaXRlclxuICAgICAgfmxlbmd0aDooY2hlY2sgKGZ1biBsZW5ndGggLT4gYXNzZXJ0IChsZW5ndGggPj0gMCkpKVxuICAgICAgfmZyb250OlxuICAgICAgICAoY2hlY2sgKGZ1biBmcm9udCAtPlxuICAgICAgICAgICBsZXQgaSA9IHJlZiB0Lmxlbmd0aCBpblxuICAgICAgICAgICBsZXQgciA9IHJlZiBmcm9udCBpblxuICAgICAgICAgICB3aGlsZSAhaSA+IDAgZG9cbiAgICAgICAgICAgICBkZWNyIGk7XG4gICAgICAgICAgICAgbGV0IGVsdCA9ICFyIGluXG4gICAgICAgICAgICAgciA6PSBVb3B0LnZhbHVlX2V4biBlbHQuRWx0Lm5leHQ7XG4gICAgICAgICAgICAgYXNzZXJ0IChVb3B0LmlzX3NvbWUgZWx0LnZhbHVlKVxuICAgICAgICAgICBkb25lO1xuICAgICAgICAgICBhc3NlcnQgKHBoeXNfZXF1YWwgIXIgdC5iYWNrKSkpXG4gICAgICB+YmFjazooY2hlY2sgKGZ1biBiYWNrIC0+IGFzc2VydCAoVW9wdC5pc19ub25lIGJhY2suRWx0LnZhbHVlKSkpXG4gICAgICB+dW51c2VkX2VsdHM6XG4gICAgICAgIChjaGVjayAoZnVuIHVudXNlZF9lbHRzIC0+XG4gICAgICAgICAgIGxldCByID0gcmVmIHVudXNlZF9lbHRzIGluXG4gICAgICAgICAgIHdoaWxlIFVvcHQuaXNfc29tZSAhciBkb1xuICAgICAgICAgICAgIGxldCBlbHQgPSBVb3B0LnZhbHVlX2V4biAhciBpblxuICAgICAgICAgICAgIHIgOj0gZWx0LkVsdC5uZXh0O1xuICAgICAgICAgICAgIGFzc2VydCAoVW9wdC5pc19ub25lIGVsdC52YWx1ZSlcbiAgICAgICAgICAgZG9uZSkpKVxuOztcblxubGV0IGNyZWF0ZSAoKSA9XG4gIGxldCBlbHQgPSBFbHQuY3JlYXRlICgpIGluXG4gIHsgZnJvbnQgPSBlbHQ7IGJhY2sgPSBlbHQ7IGxlbmd0aCA9IDA7IHVudXNlZF9lbHRzID0gVW9wdC5ub25lIH1cbjs7XG5cbmxldCBnZXRfdW51c2VkX2VsdCB0ID1cbiAgKCogQkVHSU4gQVRPTUlDIFNFQ1RJT04gKilcbiAgaWYgVW9wdC5pc19zb21lIHQudW51c2VkX2VsdHNcbiAgdGhlbiAoXG4gICAgbGV0IGVsdCA9IFVvcHQudW5zYWZlX3ZhbHVlIHQudW51c2VkX2VsdHMgaW5cbiAgICB0LnVudXNlZF9lbHRzIDwtIGVsdC5uZXh0O1xuICAgIGVsdCAoKiBFTkQgQVRPTUlDIFNFQ1RJT04gKikpXG4gIGVsc2UgRWx0LmNyZWF0ZSAoKVxuOztcblxubGV0IGVucXVldWUgKHR5cGUgYSkgKHQgOiBhIHQpIChhIDogYSkgPVxuICBsZXQgbmV3X2JhY2sgPSBnZXRfdW51c2VkX2VsdCB0IGluXG4gICgqIEJFR0lOIEFUT01JQyBTRUNUSU9OICopXG4gIHQubGVuZ3RoIDwtIHQubGVuZ3RoICsgMTtcbiAgdC5iYWNrLnZhbHVlIDwtIFVvcHQuc29tZSBhO1xuICB0LmJhY2submV4dCA8LSBVb3B0LnNvbWUgbmV3X2JhY2s7XG4gIHQuYmFjayA8LSBuZXdfYmFja1xuOztcblxuKCogRU5EIEFUT01JQyBTRUNUSU9OICopXG5cbmxldCByZXR1cm5fdW51c2VkX2VsdCB0IChlbHQgOiBfIEVsdC50KSA9XG4gICgqIEJFR0lOIEFUT01JQyBTRUNUSU9OICopXG4gIGVsdC52YWx1ZSA8LSBVb3B0Lm5vbmU7XG4gIGVsdC5uZXh0IDwtIHQudW51c2VkX2VsdHM7XG4gIHQudW51c2VkX2VsdHMgPC0gVW9wdC5zb21lIGVsdDtcbiAgKCogRU5EIEFUT01JQyBTRUNUSU9OICopXG4gICgpXG47O1xuXG5sZXRbQGNvbGRdIHJhaXNlX2RlcXVldWVfZW1wdHkgdCA9XG4gIGZhaWx3aXRocyB+aGVyZTpbJWhlcmVdIFwiVGhyZWFkX3NhZmVfcXVldWUuZGVxdWV1ZV9leG4gb2YgZW1wdHkgcXVldWVcIiB0IFslc2V4cF9vZjogXyB0XVxuOztcblxubGV0IGRlcXVldWVfZXhuIHQgPVxuICAoKiBCRUdJTiBBVE9NSUMgU0VDVElPTiAqKVxuICBpZiB0Lmxlbmd0aCA9IDAgdGhlbiByYWlzZV9kZXF1ZXVlX2VtcHR5IHQ7XG4gIGxldCBlbHQgPSB0LmZyb250IGluXG4gIGxldCBhID0gZWx0LnZhbHVlIGluXG4gIHQuZnJvbnQgPC0gVW9wdC51bnNhZmVfdmFsdWUgZWx0Lm5leHQ7XG4gIHQubGVuZ3RoIDwtIHQubGVuZ3RoIC0gMTtcbiAgKCogRU5EIEFUT01JQyBTRUNUSU9OICopXG4gIHJldHVybl91bnVzZWRfZWx0IHQgZWx0O1xuICBVb3B0LnVuc2FmZV92YWx1ZSBhXG47O1xuXG5sZXQgY2xlYXJfaW50ZXJuYWxfcG9vbCB0ID0gdC51bnVzZWRfZWx0cyA8LSBVb3B0Lm5vbmVcblxubW9kdWxlIFByaXZhdGUgPSBzdHJ1Y3RcbiAgbW9kdWxlIFVvcHQgPSBVb3B0XG5lbmRcbiJdfQ==
