
package bobj;

class Redex {

    Term point;

    Term term;

    Term next;

    Equation eq;

    int position;

    public Redex(Term point,
                 Term term) {
        this.point = point;
        this.term = term;
        this.position = -1;
    }

    public Redex(Term point,
                 Term term,
                 Equation eq) {
        this.point = point;
        this.term = term;
        this.position = -1;
        this.eq = eq;
    }

    public Term getPoint() {
        return this.point;
    }

    public Term getTerm() {
        return this.term;
    }

    @Override
    public String toString() {
        String result = "";
        result += "term = " + this.term + "\n";
        result += "point = " + this.point + "\n";
        result += "next = " + this.next + "\n";
        result += "eq " + this.eq + "\n";
        return result;

    }

}
