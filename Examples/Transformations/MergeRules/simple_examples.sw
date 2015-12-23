(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

T0 = spec

  type host
  op o1 : host -> Bool
  op o2 : host -> Bool
  op o3 : host -> Bool
  op o4 : host -> Int
endspec


T1 = spec
  import T0

  op f1(h:host,h':host):Bool = o1 h && o4 h' = 0
  op f2(h:host,h':host):Bool = ~(o1 h) && o4 h' = 1
  
  % FIXME: Mergerules bug requires that there be a subtype constraint on the domain.
  op f(h:host|true):{h':host | f1(h,h') || f2(h,h')}
  
endspec
T2 = T1 { mergeRules(f,f) }



T3 = spec
  import T0

  op f1(h:host,h':host):Bool = o1 h && o2 h && o4 h' = 0
  op f2(h:host,h':host):Bool = ~(o1 h) && o2 h && o4 h' = 1
  op f3(h:host,h':host):Bool = ~(o2 h) && o4 h' = 2  
  
  % FIXME: Mergerules bug requires that there be a subtype constraint on the domain.
  op f(h:host|true):{h':host | f1(h,h') || f2(h,h') || f3(h,h')}

endspec

T4 = T3 { mergeRules(f,f) }


T5 = spec
  import T0

  op o5 : host -> Option Int

  op f1(h:host,h':host):Bool =
    ex (i:Int) o5 h = Some i && o5 h' = Some (i+1)

  op f2(h:host,h':host):Bool =
     o5 h = None && o5 h' = Some (0 : Int)
     
  op f(h:host|true):{h':host | f1(h,h') || f2(h,h')}


endspec

T6 = T5 { mergeRules(f,f) }


T7 = spec
  import T0

  op o5 : host -> Option Int

  op f1(h:host,h':host):Bool =
    ex (i:Int, j:Int) j = o4 h &&  o5 h = Some i && o5 h' = Some (i+1)

  op f2(h:host,h':host):Bool =
     ex (j:Int) j = o4 h && o5 h = None && o5 h' = Some (0 : Int)
     
  op f(h:host|true):{h':host | f1(h,h') || f2(h,h')}


endspec

T8 = T7 { mergeRules(f,f) }

