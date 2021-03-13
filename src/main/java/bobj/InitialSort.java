
package bobj;

public class InitialSort
                         extends
                         Sort {

    public InitialSort(Sort sort) {
        super(sort.getName(), sort.getModuleName());
        props = sort.props;
    }

    public InitialSort(String name,
                       ModuleName mod) {
        super(name, mod);
    }

    @Override
    public boolean isInitial() {
        return true;
    }

    @Override
    public Sort changeModuleName(ModuleName olds,
                                 ModuleName news) {

        Sort sort = new InitialSort(getName(), getModuleName().changeModuleName(olds, news));
        sort.props = this.props;
        return sort;

    }

    @Override
    public Sort changeAbsoluteModuleName(ModuleName olds,
                                         ModuleName news) {

        Sort sort =
            new InitialSort(getName(), getModuleName().changeAbsoluteModuleName(olds, news));
        sort.props = this.props;
        return sort;

    }

    @Override
    public Sort changeParameterName(String from,
                                    String to) {

        Sort sort = new InitialSort(getName(), getModuleName().changeParameterName(from, to));
        sort.props = this.props;
        return sort;
    }

}
