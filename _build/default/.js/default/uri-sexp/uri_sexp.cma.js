// Generated by js_of_ocaml
//# buildInfo:effects=false, kind=cma, use-js-string=true, version=5.8.1

//# unitInfo: Provides: Uri_sexp
//# unitInfo: Requires: Assert_failure, Sexplib0__Sexp_conv, Sexplib0__Sexp_conv_error, Uri
(function
  (globalThis){
   "use strict";
   var
    runtime = globalThis.jsoo_runtime,
    cst = "",
    cst_Authority = "Authority",
    cst_Custom = "Custom",
    cst_Fragment = "Fragment",
    cst_Generic = "Generic",
    cst_Host = "Host",
    cst_Path = "Path",
    cst_Query = "Query",
    cst_Query_key = "Query_key",
    cst_Query_value = "Query_value",
    cst_Scheme = "Scheme",
    cst_Userinfo = "Userinfo",
    cst_fragment = "fragment",
    cst_host = "host",
    cst_lib_sexp_uri_sexp_ml_Deriv = "lib_sexp/uri_sexp.ml.Derived.component",
    cst_path = "path",
    cst_port = "port",
    cst_query = "query",
    cst_scheme = "scheme",
    cst_userinfo = "userinfo",
    caml_equal = runtime.caml_equal,
    caml_maybe_attach_backtrace = runtime.caml_maybe_attach_backtrace,
    caml_string_compare = runtime.caml_string_compare,
    caml_update_dummy = runtime.caml_update_dummy,
    caml_wrap_exception = runtime.caml_wrap_exception;
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
   function caml_call3(f, a0, a1, a2){
    return (f.l >= 0 ? f.l : f.l = f.length) == 3
            ? f(a0, a1, a2)
            : runtime.caml_call_gen(f, [a0, a1, a2]);
   }
   function caml_call8(f, a0, a1, a2, a3, a4, a5, a6, a7){
    return (f.l >= 0 ? f.l : f.l = f.length) == 8
            ? f(a0, a1, a2, a3, a4, a5, a6, a7)
            : runtime.caml_call_gen(f, [a0, a1, a2, a3, a4, a5, a6, a7]);
   }
   var
    global_data = runtime.caml_get_global_data(),
    error_source_006 = cst_lib_sexp_uri_sexp_ml_Deriv,
    error_source_018 = cst_lib_sexp_uri_sexp_ml_Deriv,
    default_081 = cst,
    error_source_055 = "lib_sexp/uri_sexp.ml.Derived.t",
    default_111 = cst,
    Uri = global_data.Uri,
    Sexplib0_Sexp_conv = global_data.Sexplib0__Sexp_conv,
    Sexplib0_Sexp_conv_error = global_data.Sexplib0__Sexp_conv_error,
    Assert_failure = global_data.Assert_failure,
    component_of_sexp = function _I_(_H_){return _I_.fun(_H_);},
    component_of_sexp$0 = function _G_(_F_){return _G_.fun(_F_);};
   caml_update_dummy
    (component_of_sexp,
     function(sexp_004){
      if(0 === sexp_004[0]){
       var
        atom_002 = sexp_004[1],
        switch$0 = caml_string_compare(atom_002, cst_Path);
       if(0 <= switch$0){
        if(0 >= switch$0) return 892015045;
        if(atom_002 === cst_Query) return -250086680;
        if(atom_002 === cst_Query_key) return -911188600;
        if(atom_002 === cst_Query_value) return 795008922;
        if(atom_002 === cst_Scheme) return -178940859;
        if(atom_002 === cst_Userinfo) return -145160103;
       }
       else{
        if(atom_002 === cst_Authority) return -715788189;
        if(atom_002 === cst_Custom)
         return caml_call2
                 (Sexplib0_Sexp_conv_error[23], error_source_006, sexp_004);
        if(atom_002 === cst_Fragment) return 127343600;
        if(atom_002 === cst_Generic) return 61643255;
        if(atom_002 === cst_Host) return 803994504;
       }
       return caml_call1(Sexplib0_Sexp_conv_error[19], 0);
      }
      var _B_ = sexp_004[1];
      if(! _B_)
       return caml_call2
               (Sexplib0_Sexp_conv_error[25], error_source_006, sexp_004);
      var match = _B_[1];
      if(0 !== match[0])
       return caml_call2
               (Sexplib0_Sexp_conv_error[24], error_source_006, sexp_004);
      var
       sexp_args_005 = _B_[2],
       atom_002$0 = match[1],
       switch$1 = caml_string_compare(atom_002$0, cst_Path);
      if(0 <= switch$1){
       if
        (0 >= switch$1
         ||
          atom_002$0 === cst_Query
          ||
           atom_002$0 === cst_Query_key
           ||
            atom_002$0 === cst_Query_value
            || atom_002$0 === cst_Scheme || atom_002$0 === cst_Userinfo)
        return caml_call2
                (Sexplib0_Sexp_conv_error[21], error_source_006, sexp_004);
      }
      else{
       if(atom_002$0 === cst_Authority)
        return caml_call2
                (Sexplib0_Sexp_conv_error[21], error_source_006, sexp_004);
       if(atom_002$0 === cst_Custom){
        if(sexp_args_005 && ! sexp_args_005[2]){
         var arg0_015 = sexp_args_005[1];
         a:
         {
          if(1 === arg0_015[0]){
           var _C_ = arg0_015[1];
           if(_C_){
            var _D_ = _C_[2];
            if(_D_){
             var _E_ = _D_[2];
             if(_E_ && ! _E_[2]){
              var
               arg2_010 = _E_[1],
               arg1_009 = _D_[1],
               arg0_008 = _C_[1],
               res0_011 = caml_call1(component_of_sexp$0, arg0_008),
               res1_012 = caml_call1(Sexplib0_Sexp_conv[31], arg1_009),
               res2_013 = caml_call1(Sexplib0_Sexp_conv[31], arg2_010),
               res0_016 = [0, res0_011, res1_012, res2_013];
              break a;
             }
            }
           }
          }
          var
           res0_016 =
             caml_call3
              (Sexplib0_Sexp_conv_error[2], error_source_006, 3, arg0_015);
         }
         return [0, -198771759, res0_016];
        }
        return caml_call3
                (Sexplib0_Sexp_conv_error[22],
                 error_source_006,
                 atom_002$0,
                 sexp_004);
       }
       if
        (atom_002$0 === cst_Fragment
         || atom_002$0 === cst_Generic || atom_002$0 === cst_Host)
        return caml_call2
                (Sexplib0_Sexp_conv_error[21], error_source_006, sexp_004);
      }
      return caml_call1(Sexplib0_Sexp_conv_error[19], 0);
     });
   caml_update_dummy
    (component_of_sexp$0,
     function(sexp_017){
      try{var _z_ = caml_call1(component_of_sexp, sexp_017); return _z_;}
      catch(_A_){
       var _y_ = caml_wrap_exception(_A_);
       if(_y_ === Sexplib0_Sexp_conv_error[18])
        return caml_call2
                (Sexplib0_Sexp_conv_error[20], error_source_018, sexp_017);
       throw caml_maybe_attach_backtrace(_y_, 0);
      }
     });
   var
    _a_ = [0, cst_Fragment],
    _b_ = [0, cst_Path],
    _c_ = [0, cst_Host],
    _d_ = [0, cst_Query_value],
    _e_ = [0, cst_Generic],
    _f_ = [0, cst_Authority],
    _g_ = [0, cst_Userinfo],
    _h_ = [0, cst_Scheme],
    _i_ = [0, cst_Query],
    _j_ = [0, cst_Query_key],
    _k_ = [0, cst_Custom];
   function sexp_of_component(param){
    if(typeof param === "number")
     return 61643255 <= param
             ? 127343600
               === param
               ? _a_
               : 803994504
                 <= param
                 ? 892015045 <= param ? _b_ : _c_
                 : 795008922 <= param ? _d_ : _e_
             : -715788189
               === param
               ? _f_
               : -178940859
                 <= param
                 ? -145160103 <= param ? _g_ : _h_
                 : -250086680 <= param ? _i_ : _j_;
    var
     v_019 = param[2],
     arg2_022 = v_019[3],
     arg1_021 = v_019[2],
     arg0_020 = v_019[1],
     res0_023 = sexp_of_component(arg0_020),
     res1_024 = caml_call1(Sexplib0_Sexp_conv[7], arg1_021),
     res2_025 = caml_call1(Sexplib0_Sexp_conv[7], arg2_022);
    return [1,
            [0,
             _k_,
             [0, [1, [0, res0_023, [0, res1_024, [0, res2_025, 0]]]], 0]]];
   }
   var
    default_073 = 0,
    default_075 = 0,
    default_077 = 0,
    default_079 = 0,
    default_084 = 0,
    _l_ = [0, "lib_sexp/uri_sexp.ml", 22, 1];
   function t_of_sexp(sexp_027){
    if(0 === sexp_027[0])
     return caml_call2
             (Sexplib0_Sexp_conv_error[16], error_source_055, sexp_027);
    var
     field_sexps_028 = sexp_027[1],
     scheme_029 = [0, 0],
     userinfo_031 = [0, 0],
     host_033 = [0, 0],
     port_035 = [0, 0],
     path_037 = [0, 0],
     query_039 = [0, 0],
     fragment_041 = [0, 0],
     duplicates_043 = [0, 0],
     extra_044 = [0, 0];
    a:
    {
     b:
     c:
     d:
     {
      e:
      {
       var param = field_sexps_028;
       for(;;){
        if(! param) break;
        var sexp_027$0 = param[1];
        if(1 !== sexp_027$0[0]) break b;
        var _u_ = sexp_027$0[1];
        if(! _u_) break c;
        var _v_ = _u_[1];
        if(0 !== _v_[0]) break e;
        var field_sexps_047 = _u_[2], field_name_045 = _v_[1];
        if(field_sexps_047 && field_sexps_047[2]) break d;
        var tail_087 = param[2];
        let field_sexps_047$0 = field_sexps_047;
        var
         field_sexp_046 =
           function(param){
            if(! field_sexps_047$0)
             return caml_call2
                     (Sexplib0_Sexp_conv_error[10], error_source_055, sexp_027);
            if(field_sexps_047$0[2])
             throw caml_maybe_attach_backtrace([0, Assert_failure, _l_], 1);
            var x_088 = field_sexps_047$0[1];
            return x_088;
           };
        if(field_name_045 !== cst_fragment)
         if(field_name_045 !== cst_host)
          if(field_name_045 !== cst_path)
           if(field_name_045 !== cst_port)
            if(field_name_045 !== cst_query)
             if(field_name_045 !== cst_scheme)
              if(field_name_045 !== cst_userinfo){
               if(Sexplib0_Sexp_conv[26][1])
                extra_044[1] = [0, field_name_045, extra_044[1]];
              }
              else if(userinfo_031[1])
               duplicates_043[1] = [0, field_name_045, duplicates_043[1]];
              else{
               var
                field_sexp_046$0 = field_sexp_046(0),
                fvalue_064 =
                  caml_call2
                   (Sexplib0_Sexp_conv[41],
                    Sexplib0_Sexp_conv[31],
                    field_sexp_046$0);
               userinfo_031[1] = [0, fvalue_064];
              }
             else if(scheme_029[1])
              duplicates_043[1] = [0, field_name_045, duplicates_043[1]];
             else{
              var
               field_sexp_046$1 = field_sexp_046(0),
               fvalue_066 =
                 caml_call2
                  (Sexplib0_Sexp_conv[41],
                   Sexplib0_Sexp_conv[31],
                   field_sexp_046$1);
              scheme_029[1] = [0, fvalue_066];
             }
            else if(query_039[1])
             duplicates_043[1] = [0, field_name_045, duplicates_043[1]];
            else{
             var
              field_sexp_046$2 = field_sexp_046(0),
              fvalue_056 =
                caml_call2
                 (Sexplib0_Sexp_conv[44],
                  function(sexp_054){
                   if(1 === sexp_054[0]){
                    var _w_ = sexp_054[1];
                    if(_w_){
                     var _x_ = _w_[2];
                     if(_x_ && ! _x_[2]){
                      var
                       arg1_051 = _x_[1],
                       arg0_050 = _w_[1],
                       res0_052 = caml_call1(Sexplib0_Sexp_conv[31], arg0_050),
                       res1_053 =
                         caml_call2
                          (Sexplib0_Sexp_conv[44], Sexplib0_Sexp_conv[31], arg1_051);
                      return [0, res0_052, res1_053];
                     }
                    }
                   }
                   return caml_call3
                           (Sexplib0_Sexp_conv_error[2], error_source_055, 2, sexp_054);
                  },
                  field_sexp_046$2);
             query_039[1] = [0, fvalue_056];
            }
           else if(port_035[1])
            duplicates_043[1] = [0, field_name_045, duplicates_043[1]];
           else{
            var
             field_sexp_046$3 = field_sexp_046(0),
             fvalue_060 =
               caml_call2
                (Sexplib0_Sexp_conv[41],
                 Sexplib0_Sexp_conv[34],
                 field_sexp_046$3);
            port_035[1] = [0, fvalue_060];
           }
          else if(path_037[1])
           duplicates_043[1] = [0, field_name_045, duplicates_043[1]];
          else{
           var
            field_sexp_046$4 = field_sexp_046(0),
            fvalue_058 = caml_call1(Sexplib0_Sexp_conv[31], field_sexp_046$4);
           path_037[1] = [0, fvalue_058];
          }
         else if(host_033[1])
          duplicates_043[1] = [0, field_name_045, duplicates_043[1]];
         else{
          var
           field_sexp_046$5 = field_sexp_046(0),
           fvalue_062 =
             caml_call2
              (Sexplib0_Sexp_conv[41],
               Sexplib0_Sexp_conv[31],
               field_sexp_046$5);
          host_033[1] = [0, fvalue_062];
         }
        else if(fragment_041[1])
         duplicates_043[1] = [0, field_name_045, duplicates_043[1]];
        else{
         var
          field_sexp_046$6 = field_sexp_046(0),
          fvalue_049 =
            caml_call2
             (Sexplib0_Sexp_conv[41],
              Sexplib0_Sexp_conv[31],
              field_sexp_046$6);
         fragment_041[1] = [0, fvalue_049];
        }
        param = tail_087;
       }
       break a;
      }
      break c;
     }
     caml_call2(Sexplib0_Sexp_conv_error[10], error_source_055, sexp_027$0);
    }
    if(duplicates_043[1])
     return caml_call3
             (Sexplib0_Sexp_conv_error[12],
              error_source_055,
              duplicates_043[1],
              sexp_027);
    if(extra_044[1])
     return caml_call3
             (Sexplib0_Sexp_conv_error[13],
              error_source_055,
              extra_044[1],
              sexp_027);
    var
     scheme_030 = scheme_029[1],
     userinfo_032 = userinfo_031[1],
     host_034 = host_033[1],
     port_036 = port_035[1],
     path_038 = path_037[1],
     query_040 = query_039[1],
     fragment_042 = fragment_041[1];
    if(fragment_042)
     var v_085 = fragment_042[1], v_085$0 = v_085;
    else
     var v_085$0 = default_084;
    if(query_040)
     var v_083 = query_040[1], v_083$0 = v_083;
    else
     var v_083$0 = 0;
    if(path_038)
     var v_082 = path_038[1], v_082$0 = v_082;
    else
     var v_082$0 = default_081;
    if(port_036)
     var v_080 = port_036[1], v_080$0 = v_080;
    else
     var v_080$0 = default_079;
    if(host_034)
     var v_078 = host_034[1], v_078$0 = v_078;
    else
     var v_078$0 = default_077;
    if(userinfo_032)
     var v_076 = userinfo_032[1], v_076$0 = v_076;
    else
     var v_076$0 = default_075;
    if(scheme_030)
     var v_074 = scheme_030[1], v_074$0 = v_074;
    else
     var v_074$0 = default_073;
    return [0, v_074$0, v_076$0, v_078$0, v_080$0, v_082$0, v_083$0, v_085$0];
   }
   var
    default_091 = 0,
    default_096 = 0,
    default_101 = 0,
    default_106 = 0,
    default_124 = 0,
    _m_ = [0, cst_scheme],
    _n_ = [0, cst_userinfo],
    _o_ = [0, cst_host],
    _p_ = [0, cst_port],
    _q_ = [0, cst_path],
    _r_ = [0, cst_query],
    _s_ = [0, cst_fragment];
   function t_of_sexp$0(sexp){
    var t = t_of_sexp(sexp);
    return caml_call8
            (Uri[11], t[1], t[2], t[3], t[4], [0, t[5]], [0, t[6]], t[7], 0);
   }
   function sexp_of_t(t){
    var
     fragment_125 = caml_call1(Uri[41], t),
     query_116 = caml_call1(Uri[13], t),
     path_112 = caml_call2(Uri[26], 0, t),
     port_107 = caml_call1(Uri[39], t),
     host_102 = caml_call1(Uri[36], t),
     userinfo_097 = caml_call2(Uri[31], 0, t),
     scheme_092 = caml_call1(Uri[29], t),
     bnds_089 = 0,
     arg_127 =
       caml_call1
        (caml_call1(Sexplib0_Sexp_conv[17], Sexplib0_Sexp_conv[7]),
         fragment_125);
    if
     (caml_equal
       (caml_call1
         (caml_call1(Sexplib0_Sexp_conv[17], Sexplib0_Sexp_conv[7]),
          default_124),
        arg_127))
     var bnds_089$0 = bnds_089;
    else
     var
      bnd_126 = [1, [0, _s_, [0, arg_127, 0]]],
      bnds_089$0 = [0, bnd_126, bnds_089];
    var _t_ = query_116 ? 0 : 1;
    if(_t_)
     var bnds_089$1 = bnds_089$0;
    else
     var
      arg_122 =
        caml_call1
         (caml_call1
           (Sexplib0_Sexp_conv[20],
            function(param){
             var
              arg1_118 = param[2],
              arg0_117 = param[1],
              res0_119 = caml_call1(Sexplib0_Sexp_conv[7], arg0_117),
              res1_120 =
                caml_call2
                 (Sexplib0_Sexp_conv[20], Sexplib0_Sexp_conv[7], arg1_118);
             return [1, [0, res0_119, [0, res1_120, 0]]];
            }),
          query_116),
      bnd_121 = [1, [0, _r_, [0, arg_122, 0]]],
      bnds_089$1 = [0, bnd_121, bnds_089$0];
    var arg_114 = caml_call1(Sexplib0_Sexp_conv[7], path_112);
    if(caml_equal(caml_call1(Sexplib0_Sexp_conv[7], default_111), arg_114))
     var bnds_089$2 = bnds_089$1;
    else
     var
      bnd_113 = [1, [0, _q_, [0, arg_114, 0]]],
      bnds_089$2 = [0, bnd_113, bnds_089$1];
    var
     arg_109 =
       caml_call1
        (caml_call1(Sexplib0_Sexp_conv[17], Sexplib0_Sexp_conv[10]), port_107);
    if
     (caml_equal
       (caml_call1
         (caml_call1(Sexplib0_Sexp_conv[17], Sexplib0_Sexp_conv[10]),
          default_106),
        arg_109))
     var bnds_089$3 = bnds_089$2;
    else
     var
      bnd_108 = [1, [0, _p_, [0, arg_109, 0]]],
      bnds_089$3 = [0, bnd_108, bnds_089$2];
    var
     arg_104 =
       caml_call1
        (caml_call1(Sexplib0_Sexp_conv[17], Sexplib0_Sexp_conv[7]), host_102);
    if
     (caml_equal
       (caml_call1
         (caml_call1(Sexplib0_Sexp_conv[17], Sexplib0_Sexp_conv[7]),
          default_101),
        arg_104))
     var bnds_089$4 = bnds_089$3;
    else
     var
      bnd_103 = [1, [0, _o_, [0, arg_104, 0]]],
      bnds_089$4 = [0, bnd_103, bnds_089$3];
    var
     arg_099 =
       caml_call1
        (caml_call1(Sexplib0_Sexp_conv[17], Sexplib0_Sexp_conv[7]),
         userinfo_097);
    if
     (caml_equal
       (caml_call1
         (caml_call1(Sexplib0_Sexp_conv[17], Sexplib0_Sexp_conv[7]),
          default_096),
        arg_099))
     var bnds_089$5 = bnds_089$4;
    else
     var
      bnd_098 = [1, [0, _n_, [0, arg_099, 0]]],
      bnds_089$5 = [0, bnd_098, bnds_089$4];
    var
     arg_094 =
       caml_call1
        (caml_call1(Sexplib0_Sexp_conv[17], Sexplib0_Sexp_conv[7]),
         scheme_092);
    if
     (caml_equal
       (caml_call1
         (caml_call1(Sexplib0_Sexp_conv[17], Sexplib0_Sexp_conv[7]),
          default_091),
        arg_094))
     var bnds_089$6 = bnds_089$5;
    else
     var
      bnd_093 = [1, [0, _m_, [0, arg_094, 0]]],
      bnds_089$6 = [0, bnd_093, bnds_089$5];
    return [1, bnds_089$6];
   }
   function compare(a, b){return caml_call2(Uri[2], a, b);}
   function equal(a, b){return caml_call2(Uri[3], a, b);}
   var
    Uri_sexp =
      [0,
       component_of_sexp$0,
       sexp_of_component,
       t_of_sexp$0,
       sexp_of_t,
       compare,
       equal];
   runtime.caml_register_global(57, Uri_sexp, "Uri_sexp");
   return;
  }
  (globalThis));

//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLjAsImZpbGUiOiJ1cmlfc2V4cC5jbWEuanMiLCJzb3VyY2VSb290IjoiIiwibmFtZXMiOlsiZXJyb3Jfc291cmNlXzAwNiIsImVycm9yX3NvdXJjZV8wMTgiLCJkZWZhdWx0XzA4MSIsImVycm9yX3NvdXJjZV8wNTUiLCJkZWZhdWx0XzExMSIsImNvbXBvbmVudF9vZl9zZXhwIiwiY29tcG9uZW50X29mX3NleHAkMCIsInNleHBfMDA0IiwiYXRvbV8wMDIiLCJzZXhwX2FyZ3NfMDA1IiwiYXRvbV8wMDIkMCIsImFyZzBfMDE1IiwiYXJnMl8wMTAiLCJhcmcxXzAwOSIsImFyZzBfMDA4IiwicmVzMF8wMTEiLCJyZXMxXzAxMiIsInJlczJfMDEzIiwicmVzMF8wMTYiLCJzZXhwXzAxNyIsInNleHBfb2ZfY29tcG9uZW50Iiwidl8wMTkiLCJhcmcyXzAyMiIsImFyZzFfMDIxIiwiYXJnMF8wMjAiLCJyZXMwXzAyMyIsInJlczFfMDI0IiwicmVzMl8wMjUiLCJkZWZhdWx0XzA3MyIsImRlZmF1bHRfMDc1IiwiZGVmYXVsdF8wNzciLCJkZWZhdWx0XzA3OSIsImRlZmF1bHRfMDg0IiwidF9vZl9zZXhwIiwic2V4cF8wMjciLCJmaWVsZF9zZXhwc18wMjgiLCJzY2hlbWVfMDI5IiwidXNlcmluZm9fMDMxIiwiaG9zdF8wMzMiLCJwb3J0XzAzNSIsInBhdGhfMDM3IiwicXVlcnlfMDM5IiwiZnJhZ21lbnRfMDQxIiwiZHVwbGljYXRlc18wNDMiLCJleHRyYV8wNDQiLCJzZXhwXzAyNyQwIiwiZmllbGRfc2V4cHNfMDQ3IiwiZmllbGRfbmFtZV8wNDUiLCJ0YWlsXzA4NyIsImZpZWxkX3NleHBzXzA0NyQwIiwiZmllbGRfc2V4cF8wNDYiLCJ4XzA4OCIsImZpZWxkX3NleHBfMDQ2JDAiLCJmdmFsdWVfMDY0IiwiZmllbGRfc2V4cF8wNDYkMSIsImZ2YWx1ZV8wNjYiLCJmaWVsZF9zZXhwXzA0NiQyIiwiZnZhbHVlXzA1NiIsInNleHBfMDU0IiwiYXJnMV8wNTEiLCJhcmcwXzA1MCIsInJlczBfMDUyIiwicmVzMV8wNTMiLCJmaWVsZF9zZXhwXzA0NiQzIiwiZnZhbHVlXzA2MCIsImZpZWxkX3NleHBfMDQ2JDQiLCJmdmFsdWVfMDU4IiwiZmllbGRfc2V4cF8wNDYkNSIsImZ2YWx1ZV8wNjIiLCJmaWVsZF9zZXhwXzA0NiQ2IiwiZnZhbHVlXzA0OSIsInNjaGVtZV8wMzAiLCJ1c2VyaW5mb18wMzIiLCJob3N0XzAzNCIsInBvcnRfMDM2IiwicGF0aF8wMzgiLCJxdWVyeV8wNDAiLCJmcmFnbWVudF8wNDIiLCJ2XzA4NSIsInZfMDg1JDAiLCJ2XzA4MyIsInZfMDgzJDAiLCJ2XzA4MiIsInZfMDgyJDAiLCJ2XzA4MCIsInZfMDgwJDAiLCJ2XzA3OCIsInZfMDc4JDAiLCJ2XzA3NiIsInZfMDc2JDAiLCJ2XzA3NCIsInZfMDc0JDAiLCJkZWZhdWx0XzA5MSIsImRlZmF1bHRfMDk2IiwiZGVmYXVsdF8xMDEiLCJkZWZhdWx0XzEwNiIsImRlZmF1bHRfMTI0IiwidF9vZl9zZXhwJDAiLCJzZXhwIiwidCIsInNleHBfb2ZfdCIsImZyYWdtZW50XzEyNSIsInF1ZXJ5XzExNiIsInBhdGhfMTEyIiwicG9ydF8xMDciLCJob3N0XzEwMiIsInVzZXJpbmZvXzA5NyIsInNjaGVtZV8wOTIiLCJibmRzXzA4OSIsImFyZ18xMjciLCJibmRzXzA4OSQwIiwiYm5kXzEyNiIsImJuZHNfMDg5JDEiLCJhcmdfMTIyIiwiYXJnMV8xMTgiLCJhcmcwXzExNyIsInJlczBfMTE5IiwicmVzMV8xMjAiLCJibmRfMTIxIiwiYXJnXzExNCIsImJuZHNfMDg5JDIiLCJibmRfMTEzIiwiYXJnXzEwOSIsImJuZHNfMDg5JDMiLCJibmRfMTA4IiwiYXJnXzEwNCIsImJuZHNfMDg5JDQiLCJibmRfMTAzIiwiYXJnXzA5OSIsImJuZHNfMDg5JDUiLCJibmRfMDk4IiwiYXJnXzA5NCIsImJuZHNfMDg5JDYiLCJibmRfMDkzIiwiY29tcGFyZSIsImEiLCJiIiwiZXF1YWwiXSwic291cmNlcyI6WyIvVXNlcnMvamFjb2J6aWZmLy5v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QkFJZUMsU0FKZko7SUFHZTtLQUFBSztPQUFBO1NBQUEsMkRBQUFwQjtJQUFBO01BQUE7UUFBQTtVQUFBO1VBQU5YO1FBQU0rQjtTQUhmQyxhQUFBSDs7S0FHZTtNQUFBSSwyQkFBQUY7TUFIZkMsaUJBR2VDLFNBSGZKO0lBRW1CO0tBQUFLO09BQUE7U0FBQTtTQUFBdEI7SUFBQTtNQUFBO1FBQUE7VUFBQTtVQUFWYjtRQUFVbUM7U0FGbkJDLGFBQUFIOztLQUVtQjtNQUFBSSwyQkFBQUY7TUFGbkJDLGlCQUVtQkMsU0FGbkJKO0lBQ2lCO0tBQUFLO09BQUE7U0FBQTtTQUFBeEI7SUFBQTtNQUFBO1FBQUE7VUFBQTtVQUFSZjtRQUFRdUM7U0FEakJDLGFBQUFIOztLQUNpQjtNQUFBSSwyQkFBQUY7TUFEakJDLGlCQUNpQkMsU0FEakJKO0lBQUEsV0FBQUc7R0FzQ0M7WUFHRUUsUUFBUUMsR0FBRUMsR0FBSSxPQUFBLG1CQUFORCxHQUFFQyxHQUFtQjtZQUM3QkMsTUFBTUYsR0FBRUMsR0FBSSxPQUFBLG1CQUFORCxHQUFFQyxHQUFpQjs7OztPQTVCekJsSTtPQUNBYztPQUVBNkU7T0FZQUc7T0FZQWtDO09BQ0FHOzs7RSIsInNvdXJjZXNDb250ZW50IjpbIm9wZW4gVXJpXG5cbm1vZHVsZSBEZXJpdmVkID1cbnN0cnVjdFxuXG5cdG9wZW4gU2V4cGxpYjAuU2V4cF9jb252XG5cblx0dHlwZSBjb21wb25lbnQgPSBbXG5cdCAgfCBgU2NoZW1lXG5cdCAgfCBgQXV0aG9yaXR5XG5cdCAgfCBgVXNlcmluZm8gKCogc3ViY29tcG9uZW50IG9mIGF1dGhvcml0eSBpbiBzb21lIHNjaGVtZXMgKilcblx0ICB8IGBIb3N0ICgqIHN1YmNvbXBvbmVudCBvZiBhdXRob3JpdHkgaW4gc29tZSBzY2hlbWVzICopXG5cdCAgfCBgUGF0aFxuXHQgIHwgYFF1ZXJ5XG5cdCAgfCBgUXVlcnlfa2V5XG5cdCAgfCBgUXVlcnlfdmFsdWVcblx0ICB8IGBGcmFnbWVudFxuICAgICAgICAgIHwgYEdlbmVyaWNcbiAgICAgICAgICB8IGBDdXN0b20gb2YgKGNvbXBvbmVudCAqIHN0cmluZyAqIHN0cmluZylcblx0XSBbQEBkZXJpdmluZyBzZXhwXVxuXG5cdHR5cGUgdCA9IHtcbiAgICAgICAgICBzY2hlbWU6IHN0cmluZyBvcHRpb24gW0BkZWZhdWx0IE5vbmVdIFtAc2V4cF9kcm9wX2RlZmF1bHQuc2V4cF07XG4gICAgICAgICAgdXNlcmluZm86IHN0cmluZyBvcHRpb24gW0BkZWZhdWx0IE5vbmVdIFtAc2V4cF9kcm9wX2RlZmF1bHQuc2V4cF07XG4gICAgICAgICAgaG9zdDogc3RyaW5nIG9wdGlvbiBbQGRlZmF1bHQgTm9uZV0gW0BzZXhwX2Ryb3BfZGVmYXVsdC5zZXhwXTtcbiAgICAgICAgICBwb3J0OiBpbnQgb3B0aW9uIFtAZGVmYXVsdCBOb25lXSBbQHNleHBfZHJvcF9kZWZhdWx0LnNleHBdO1xuICAgICAgICAgIHBhdGg6IHN0cmluZyBbQGRlZmF1bHQgXCJcIl0gW0BzZXhwX2Ryb3BfZGVmYXVsdC5zZXhwXTtcbiAgICAgICAgICBxdWVyeTogKHN0cmluZyAqIHN0cmluZyBsaXN0KSBsaXN0IFtAc2V4cC5saXN0XTtcbiAgICAgICAgICBmcmFnbWVudDogc3RyaW5nIG9wdGlvbiBbQGRlZmF1bHQgTm9uZV0gW0BzZXhwX2Ryb3BfZGVmYXVsdC5zZXhwXVxuXHR9IFtAQGRlcml2aW5nIHNleHBdXG5cbmVuZFxuXG5vcGVuIERlcml2ZWRcblxubGV0IGNvbXBvbmVudF9vZl9zZXhwID0gY29tcG9uZW50X29mX3NleHBcbmxldCBzZXhwX29mX2NvbXBvbmVudCA9IHNleHBfb2ZfY29tcG9uZW50XG5cbmxldCB0X29mX3NleHAgc2V4cCA9XG5cdGxldCB0ID0gdF9vZl9zZXhwIHNleHAgaW5cblx0VXJpLm1ha2Vcblx0XHQ/c2NoZW1lOnQuc2NoZW1lXG5cdFx0P3VzZXJpbmZvOnQudXNlcmluZm9cblx0XHQ/aG9zdDp0Lmhvc3Rcblx0XHQ/cG9ydDp0LnBvcnRcblx0XHR+cGF0aDp0LnBhdGhcblx0XHR+cXVlcnk6dC5xdWVyeVxuXHRcdD9mcmFnbWVudDp0LmZyYWdtZW50XG5cdFx0KClcblxubGV0IHNleHBfb2ZfdCB0ID1cblx0c2V4cF9vZl90IHtcblx0XHRzY2hlbWUgPSBzY2hlbWUgdDtcblx0XHR1c2VyaW5mbyA9IHVzZXJpbmZvIHQ7XG5cdFx0aG9zdCA9IGhvc3QgdDtcblx0XHRwb3J0ID0gcG9ydCB0O1xuXHRcdHBhdGggPSBwYXRoIHQ7XG5cdFx0cXVlcnkgPSBxdWVyeSB0O1xuXHRcdGZyYWdtZW50ID0gZnJhZ21lbnQgdFxuXHR9XG5cbnR5cGUgY29tcG9uZW50ID0gVXJpLmNvbXBvbmVudFxubGV0IGNvbXBhcmUgYSBiID0gVXJpLmNvbXBhcmUgYSBiXG5sZXQgZXF1YWwgYSBiID0gVXJpLmVxdWFsIGEgYlxudHlwZSB0ID0gVXJpLnRcbiJdfQ==
