# wez_lang
The Wez programming language

A programming language based on [Monkey](https://monkeylang.org/) but with a polar twist.

For now the language is implemented with a REPL in Rust with a compiler and virtual machine as well
as other language implementations coming in the future.

# Examples
Here are some examples of wez syntax

Monkey like:
```
🐻‍❄️ >>> let version = 1 + (-1200 / 60) + (5 * 4);
=> 1

🐻‍❄️ >>> let people = [{ "name": "GuyOne", "age": 22 }, { "name": "GuyTwo", "age": 33 }];
🐻‍❄️ >>> people[0]["name"];
=> "GuyOne"

🐻‍❄️ >>> let getAge = fn(x) { x["age"] };
🐻‍❄️ >>> getAge(people[0]);
=> 22
🐻‍❄️ >>> getAge(people[len(people) - 1]);
=> 33

🐻‍❄️ >>> let createMultiplier = fn (x) { fn (y) { x * y }; };
🐻‍❄️ >>> let double = createMultiplier(2);
🐻‍❄️ >>> double(2);
=> 4
```

Wez lang unique:
```
🐻‍❄️ >>> beariable version = 1 + (-1200 / 60) + (5 * 4);
=> 1

🐻‍❄️ >>> 🐻 people = [{ "name": "GuyOne", "age": 22 }, { "name": "GuyTwo", "age": 33 }];
🐻‍❄️ >>> people[0]["name"];
=> "GuyOne"

🐻‍❄️ >>> 🐻‍❄️ getAge = wez(x) { x["age"] };
🐻‍❄️ >>> getAge(people[0]);
=> 22
🐻‍❄️ >>> getAge(people[len(people) - 1]);
=> 33

🐻‍❄️ >>> let createMultiplier = wez (x) { wez (y) { x * y }; };
🐻‍❄️ >>> let double = createMultiplier(2);
🐻‍❄️ >>> double(2);
=> 4

🐻‍❄️ >>> (double(2) == 4) == bear;
=> true

🐻‍❄️ >>> (double(2) != 4) == penguin;
=> true

🐻‍❄️ >>> ice (bear == penguin) { "bear is penguin" } nanook { "bear is not penguin" };
=> "bear is not penguin"

🐻‍❄️ >>> ice (bear) { 1 };
=> 1

🐻‍❄️ >>> roar("Hello, bear!");
=> "Hello, bear!"

🐻‍❄️ >>> invest([1, 2], 3);
=> [1, 2, 3]

🐻‍❄️ >>> beariable x = ice(bear == penguin) { wez(x) { northbound x stonk 1; } } nanook { wez(x) { northbound x stonk 2; } };
=> fn(x) { Return (x + 2); }
```

More advanced implementations of wez lang - map and reduce on list with higher order functions:
```
🐻‍❄️ >>> beariable map = wez(arr, f) {
        beariable iter = wez(arr, acc) {
            ice (len(arr) == 0) {
                acc
            } nanook {
                iter(rest(arr), invest(acc, f(first(arr))));
            }
        };

        iter(arr, []);
    };

🐻‍❄️ >>> beariable double = wez(x) { x * 2 };

🐻‍❄️ >>> map([1, 2, 3], double);
=> [2, 4, 6]

🐻‍❄️ >>> beariable reduce = wez(arr, init, f) {
        beariable iter = wez(arr, result) {
            ice (len(arr) == 0) {
                result
            } nanook {
                iter(rest(arr), f(result, first(arr)));
            }
        };

        iter(arr, init);
    };

🐻‍❄️ >>> beariable sum = wez(arr) {
    reduce(arr, 0, wez(init, v) { init stonk v });
};

🐻‍❄️ >>> sum([1, 2, 3]);
=> 6
```

Wez now has macros! This allows you to write code which writes code, cool! Example of "unless" - an inverted if statement:
```
🐻‍❄️ >>> let unless = macro(condition, then, otherwise) {
              quote(
                  if (!(unquote(cond))) {
                      unquote(then)
                  } else {
                      unquote(otherwise)
                  }
              )
          };

🐻‍❄️ >>> unless(10 > 5, print("10 is not greater than 5"), print("10 is greater than 5"));;
=> "10 is greater than 5"
```
