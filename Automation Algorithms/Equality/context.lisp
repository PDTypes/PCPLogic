(defun putdown_on_stack(x y) (cons (cons `(holding ,x) (cons `(clear ,y) nil)) (cons `(not (holding ,x)) (cons `(not (clear ,y)) (cons `(on ,x ,y) (cons `(handempty) nil))))))
(defun pickup_from_table(x) (cons (cons `(handempty) (cons `(ontable ,x) (cons `(clear ,x) nil))) (cons `(not (handempty)) (cons `(not (ontable ,x)) (cons `(holding ,x) nil)))))
