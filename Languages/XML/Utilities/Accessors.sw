(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

XML qualifying
spec
 import ../Utilities/XML_Base
 import ../Utilities/XML_Unicode
 import ../XML_Sig

 op find_attribute_ustring (element: Element, target: UString) : Option ElementAttribute =
   let
     def find_attr tag =
       foldr (fn (attr, result) ->
                if attr.name = target then
                  Some attr
                else
                  result)
             None
             tag.attributes
   in
   case element of
     | Empty tag -> find_attr tag
     | Full {stag, content, etag} -> find_attr stag

 op find_attribute (x: Element, target: String) : Option ElementAttribute =
   find_attribute_ustring (x, ustring target)

 op find_element_ustring (x: Element, target: UString, recursive? : Bool) : Option Element =
   case x of
     | Empty _ -> None
     | Full {stag, content, etag} ->
       foldr (fn ((_, item), result) ->
                case item of
                  | Element child ->
                    if element_name child = target then
                      Some child
                    else if recursive? then
                      find_element_ustring (x, target, true)
                    else
                      result
                  | _ -> result)
             None
             content.items

 op find_element (x: Element, target: String, recursive? : Bool) : Option Element =
   find_element_ustring (x, ustring target, recursive?)

end-spec
