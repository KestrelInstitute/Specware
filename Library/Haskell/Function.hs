module Function ( module Function, module Boolean ) where
import Boolean

function__injective_p :: (Eq b, Eq a) => (a -> b) -> Bool
function__injective_p f = error "Trying to evaluate a univeral quanitification."

function__surjective_p :: Eq b => (a -> b) -> Bool
function__surjective_p f = 
  error "Trying to evaluate a univeral quanitification."

function__bijective_p :: (Eq b, Eq a) => (a -> b) -> Bool
function__bijective_p f = 
  function__injective_p f && function__surjective_p f

function__inverse :: Eq b => (a -> b) -> b -> a
function__inverse f y = error "Trying to evaluate a \"the\" expression."