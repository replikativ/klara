(ns awfy.towers
  "Are We Fast Yet? Towers of Hanoi. The original mutates linked stacks; here
  the piles are persistent lists threaded through the moves.")

(defn push-disk [piles disk pile]
  (let [top (peek (nth piles pile))]
    (if (and top (<= top disk))
      (throw (ex-info "Cannot put a big disk on a smaller one" {:disk disk}))
      (update piles pile conj disk))))

(defn move-top-disk [[piles moves] from to]
  (let [disk (peek (nth piles from))]
    [(push-disk (update piles from pop) disk to) (inc moves)]))

(defn move-disks [state disks from to]
  (if (= disks 1)
    (move-top-disk state from to)
    (let [other (- 3 from to)]
      (-> state
          (move-disks (dec disks) from other)
          (move-top-disk from to)
          (move-disks (dec disks) other to)))))

(defn build-tower [piles pile disks]
  (reduce (fn [ps i] (push-disk ps i pile)) piles (range disks -1 -1)))

(defn run [] (second (move-disks [(build-tower [() () ()] 0 13) 0] 13 0 1)))
(def expected 8191)
