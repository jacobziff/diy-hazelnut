// Generated by js_of_ocaml
//# buildInfo:effects=false, kind=cma, use-js-string=true, version=5.8.1

//# unitInfo: Provides: Monad_lib
(function
  (globalThis){
   "use strict";
   var runtime = globalThis.jsoo_runtime, Monad_lib = [0];
   runtime.caml_register_global(0, Monad_lib, "Monad_lib");
   return;
  }
  (globalThis));

//# unitInfo: Provides: Monad_lib__Monad
(function(globalThis){
   "use strict";
   var runtime = globalThis.jsoo_runtime;
   function caml_call1(f, a0){
    return (f.l >= 0 ? f.l : f.l = f.length) == 1
            ? f(a0)
            : runtime.caml_call_gen(f, [a0]);
   }
   function let$0(x, f){
    if(! x) return 0;
    var x$0 = x[1];
    return caml_call1(f, x$0);
   }
   function let$1(x, f){
    if(! x) return 0;
    var x$0 = x[1];
    return [0, caml_call1(f, x$0)];
   }
   var Monad_lib_Monad = [0, let$0, let$1];
   runtime.caml_register_global(0, Monad_lib_Monad, "Monad_lib__Monad");
   return;
  }
  (globalThis));

//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLjAsImZpbGUiOiIubW9uYWRfbGliLm9ianMvanNvby9kZWZhdWx0L21vbmFkX2xpYi5jbWEuanMiLCJzb3VyY2VSb290IjoiIiwibmFtZXMiOlsibGV0JDAiLCJ4IiwiZiIsIngkMCIsImxldCQxIl0sInNvdXJjZXMiOlsiL1VzZXJzL2phY29iemlmZi9Eb2N1bWVudHMvQ29kaW5nL0hhemVsOk9DYW1sL0ZQIExhYi9kaXktaGF6ZWxudXQvX2J1aWxkL2RlZmF1bHQvbW9uYWQvbW9uYWQucmUiXSwibWFwcGluZ3MiOiI7Ozs7Ozs7Ozs7RTs7Ozs7OztHOzs7OztZQUFJQSxNQUFZQyxHQUFlQztJQUM3QixLQURjRCxHQUdKO1FBREhFLE1BRk9GO0lBRUQsT0FBQSxXQUZnQkMsR0FFdEJDO0dBRU47WUFFQ0MsTUFOWUgsR0FNYUM7SUFBNEIsS0FOekNELEdBR0o7UUFJTEUsTUFQU0Y7SUFRZCxXQUFLLFdBRnNCQyxHQUN0QkM7R0FFTjs2QkFUR0gsT0FNQUk7OztFIiwic291cmNlc0NvbnRlbnQiOlsibGV0ICggbGV0KiApID0gKHg6IG9wdGlvbignYSksIGY6ICdhID0+IG9wdGlvbignYikpOiBvcHRpb24oJ2IpID0+XG4gIHN3aXRjaCAoeCkge1xuICB8IFNvbWUoeCkgPT4gZih4KVxuICB8IE5vbmUgPT4gTm9uZVxuICB9O1xuXG5sZXQgKGxldCspID0gKHg6IG9wdGlvbignYSksIGY6ICdhID0+ICdiKTogb3B0aW9uKCdiKSA9PiB7XG4gIGxldCogeCA9IHg7XG4gIFNvbWUoZih4KSk7XG59O1xuIl19
