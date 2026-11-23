use std::collections::HashMap;

fn optimal_or_depth(n: usize) -> usize {
    assert!(n <= 16);
    fn solve(mask: u32, n: usize, memo: &mut HashMap<u32, usize>) -> usize {
        if mask.count_ones() as usize == n { return 0; }
        if let Some(&v) = memo.get(&mask) { return v; }
        let v = (0..n)
            .filter(|&i| mask & (1u32 << i) == 0)
            .map(|i| 1 + solve(mask | (1u32 << i), n, memo))
            .min().unwrap();
        memo.insert(mask, v);
        v
    }
    solve(0, n, &mut HashMap::new())
}

#[derive(Clone, Copy, Debug)]
struct Lit { variable: usize, positive: bool }
impl Lit {
    fn node(self) -> usize { 2 * self.variable + usize::from(self.positive) }
    fn neg(self) -> Self { Self { positive: !self.positive, ..self } }
    fn eval(self, x: &[bool]) -> bool { x[self.variable] == self.positive }
}

fn solve_2sat(n: usize, clauses: &[(Lit, Lit)]) -> Option<Vec<bool>> {
    let mut adj = vec![vec![]; 2*n];
    let mut rev = vec![vec![]; 2*n];
    for &(a,b) in clauses {
        assert!(a.variable < n && b.variable < n);
        for (u,v) in [(a.neg().node(), b.node()), (b.neg().node(), a.node())] {
            adj[u].push(v);
            rev[v].push(u);
        }
    }
    let mut seen=vec![false;2*n];
    let mut order=vec![];
    for start in 0..2*n {
        if seen[start] {continue;}
        seen[start]=true;
        let mut stack=vec![(start,0usize)];
        while let Some((v,next))=stack.last_mut() {
            if *next < adj[*v].len() {
                let u=adj[*v][*next];
                *next+=1;
                if !seen[u] {seen[u]=true; stack.push((u,0));}
            } else {
                let v=*v;
                stack.pop();
                order.push(v);
            }
        }
    }
    let mut comp=vec![usize::MAX;2*n];
    let mut count=0;
    for &s in order.iter().rev() {
        if comp[s]!=usize::MAX {continue;}
        comp[s]=count;
        let mut stack=vec![s];
        while let Some(v)=stack.pop() {
            for &u in &rev[v] {
                if comp[u]==usize::MAX {comp[u]=count;stack.push(u);}
            }
        }
        count+=1;
    }
    let mut answer=vec![false;n];
    for i in 0..n {
        if comp[2*i]==comp[2*i+1] {return None;}
        answer[i]=comp[2*i+1]>comp[2*i];
    }
    assert!(clauses.iter().all(|(a,b)|a.eval(&answer)||b.eval(&answer)));
    Some(answer)
}

fn brute(n:usize, clauses:&[(Lit,Lit)]) -> bool {
    (0..(1usize<<n)).any(|mask| {
        let x:Vec<bool>=(0..n).map(|i|(mask & (1<<i))!=0).collect();
        clauses.iter().all(|(a,b)|a.eval(&x)||b.eval(&x))
    })
}

fn exhaustive_tests() -> usize {
    let mut checked=0;
    for n in 1..=3 {
        let lits:Vec<Lit>=(0..n).flat_map(|variable|
            [false,true].map(move |positive|Lit{variable,positive})).collect();
        let pairs:Vec<(Lit,Lit)>=lits.iter().flat_map(|&a|lits.iter().map(move |&b|(a,b))).collect();
        for &a in &pairs {for &b in &pairs {for &c in &pairs {
            let formula=[a,b,c];
            let result=solve_2sat(n,&formula);
            assert_eq!(result.is_some(),brute(n,&formula));
            checked+=1;
        }}}
    }
    checked
}

fn main() {
    assert_eq!(optimal_or_depth(16),16);
    assert_eq!(exhaustive_tests(),50_816);
    println!("PASS: black-box OR and 50,816 2-CNF instances");
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn oracle() {for n in [0,1,2,4,8,16] {assert_eq!(optimal_or_depth(n),n);}}
    #[test] fn sat() {assert_eq!(exhaustive_tests(),50_816);}
    #[test] fn contradictory() {
        let a=Lit{variable:0,positive:true};
        assert!(solve_2sat(1,&[(a,a),(a.neg(),a.neg())]).is_none());
    }
}
