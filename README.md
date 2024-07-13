Just an version update list.

0713: 在决定写归纳的 nat 函数用什么形式时发现写成 Fixpoint 的归纳是很不平凡的, 测试了各种情况.

0712: 把 Empty/Bot 和 Unit/Top 拆成了四种类型, 分别给了不一样的意义. 稍微实现了一点 normalizing 的 infrastructure. 晚上又学到上面四个类型和 subtype 和在有 side-effect 的语言中的作用.

0711: hastype 和 subtype 的计算版本. 比对了一下发现normalizing精确到小标题都是一样的

0710: value和step的可计算版本, Notation 的使用

0708: 各种 Type 层的 Notation 以及 setoid rewrite 的使用, 因为要计算的话连函数外延都不能用. setoid morphism 的始对象是 eq.