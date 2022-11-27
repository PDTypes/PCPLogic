(defun putdown_on_stack(x y) (cons (cons `(holding ,x) (cons `(clear ,y) nil)) (cons `(not (holding ,x)) (cons `(not (clear ,y)) (cons `(on ,x ,y) (cons `(handempty) nil))))))
(defun pickup_from_stack(x y) (cons (cons `(on ,x ,y) (cons `(clear ,x) (cons `(handempty) nil))) (cons `(not (on ,x ,y)) (cons `(not (handempty)) (cons `(holding ,x) (cons `(clear ,y) nil))))))
(defun putdown_on_table(x) (cons (cons `(holding ,x) nil) (cons `(not (holding ,x)) (cons `(ontable ,x) (cons `(handempty) nil)))))
(defun pickup_from_table(x) (cons (cons `(handempty) (cons `(ontable ,x) (cons `(clear ,x) nil))) (cons `(not (handempty)) (cons `(not (ontable ,x)) (cons `(holding ,x) nil)))))
