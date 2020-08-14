import esprima
import parser.parse

if __name__ == "__main__" :
    with open("/Users/teo/Desktop/notebooks/a.js","r") as f :
        aaa = f.read()
    try :
        source = esprima.parseScript(aaa)
        print(parse(source))
    except Exception as ex:
        print(f"ERROR: {ex}")
        exit()