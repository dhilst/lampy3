;;; lampy-mode.el --- lampy syntax highlighting

;; Copyright © 2016, by Preston Moore

;; Author: Daniel Hilst (danielhilst@gmail.com)
;; Version: 0.0.1
;; Keywords: languages

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This package provides a major mode with highlighting for
;; `lampy'.

;;; Code:

;; create the list for font-lock.
;; each category of keyword is given a particular face
(defvar lampy-font-lock-keywords)
(setq lampy-font-lock-keywords `(
                                 ("\\(fun\\|if\\|then\\|else\\|end\\|from\\|import\\)" . font-lock-keyword-face)
                                 ("\\(#.*\\)" . font-lock-comment-face)
                                 ("[0-9]+" . font-lock-constant-face)
                                 ("\\(true\\|false\\)" . font-lock-constant-face)
                                  )
)

;;;###autoload
(define-derived-mode lampy-mode fundamental-mode
  "lampy"
  "Major mode for lampy output."
  (setq font-lock-defaults '((lampy-font-lock-keywords)))
)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.ly\\'" . lampy-mode))

;; add the mode to the `features' list
(provide 'lampy-mode)

;; Local Variables:
;; coding: utf-8
;; End:

;;; lampy-mode.el ends here
