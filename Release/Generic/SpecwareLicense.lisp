;;; This function arranges for the license message to be displayed
;;; when Specware starts up.
;;; 
;;; The *restart-init-function* variable is examined by ACL during start-up.
;;; If it is not nil, then it should be a 0-ary function that is executed
;;; immediately prior to invoking the read-eval-print loop.
;;; In earlier versions of Specware, *restart-init-function* was used to
;;; load patches. If this is needed in the future, one should be sure that the
;;; license statement that follows is displayed last on the screen *after*
;;; loading the patches and immediately before prompting the user.

#+cmu (defvar *restart-init-function*)

(setf *restart-init-function*
   #'(lambda ()
       (format t "~%                              Specware ~A
\"Specware (tm)\" is a registered trademark of Kestrel Development
Corp.

Notice: This program is protected under international and U.S. copyright
laws as an unpublished work, which is confidential and proprietary
to Kestrel Institute, Kestrel Development Corporation and Kestrel
Technology, LLC.

Its reproduction or disclosure, in whole or in part, or the production
of derivative works therefrom without the express signed permission
of Kestrel Institute,  Kestrel Development Corporation and Kestrel
Technology, LLC is prohibited.

Copyright (c) 1988-2005 by Kestrel Institute, Kestrel Development
Corporation and Kestrel Technology, LLC. All rights reserved.

Use of a copyright notice is precautionary only and does not imply
publication or disclosure.

This material may be reproduced by or for the US Government pursuant to
the copyright license under the clause DFARS 252.227-7013 (Nov 1995).

Kestrel Institute           
Kestrel Development Corporation
Kestrel Technology, LLC

3260 Hillview Ave.          
2nd Floor                  
Palo Alto, CA, 94304      

Phone/FAX: (650) 320-8888
Email: info@kt-llc.com" Specware-version)))

;; The phone/FAX number is that for KT.
