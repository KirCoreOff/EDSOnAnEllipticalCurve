using System.Text;
using System.Numerics;
using System.Security.Cryptography;

namespace ECPonElypt
{
    public class Math
    {
        public static BigInteger Mod(BigInteger n, BigInteger d)
        {
            BigInteger result = n % d;

            if (result < 0)
                result += d;

            return result;
        }


        public static BigInteger Ext_Euclidian(BigInteger a, BigInteger b)
        {
            BigInteger r = new BigInteger();
            BigInteger x = new BigInteger();
            BigInteger x1 = new BigInteger(0);
            BigInteger x2 = new BigInteger(1);
            BigInteger q = new BigInteger();
            BigInteger reserve_b = b;

            if (a < 1)
                a += reserve_b;

            while (b != 0)
            {
                q = a / b;
                r = a - q * b;
                x = x2 - q * x1;
                a = b;
                b = r;
                x2 = x1;
                x1 = x;
            }

            while (x2 < 0)
                x2 += reserve_b;

            return x2;
        }
    }

    public class EC_point
    {
        BigInteger a;
        public BigInteger A
        {
            get
            {
                return a;
            }
        }

        BigInteger b;
        public BigInteger B
        {
            get
            {
                return b;
            }
        }

        BigInteger x;
        public BigInteger X
        {
            get
            {
                return x;
            }
        }

        BigInteger y;
        public BigInteger Y
        {
            get
            {
                return y;
            }
        }

        BigInteger p;
        public BigInteger P
        {
            get
            {
                return p;
            }
        }

        public EC_point(BigInteger a, BigInteger b, BigInteger p, BigInteger x, BigInteger y)
        {
            this.a = a;
            this.b = b;
            this.p = p;
            this.x = x;
            this.y = y;
        }

        public static EC_point operator +(EC_point point1, EC_point point2)
        {
            if (point1.A != point2.A || point1.B != point2.B || point1.P != point2.P)
                throw new Exception("сложение точек разных кривых");


            BigInteger lambda;

            if (point1 != point2)
            {
                BigInteger delta_y = (point2.Y - point1.Y) > 0 ? point2.Y - point1.Y : point2.Y - point1.Y + point1.P;
                BigInteger delta_x = (point2.X - point1.X) > 0 ? point2.X - point1.X : point2.X - point1.X + point1.P;

                if (delta_x == 0)
                    throw new Exception("при сложении точек получили точку О");

                lambda = delta_y * Math.Ext_Euclidian(delta_x, point1.P);
            }
            else
            {
                lambda = (3 * (point1.X * point1.X) + point1.A) * Math.Ext_Euclidian(2 * point1.Y, point1.p);
            }

            BigInteger X = Math.Mod(lambda * lambda - point1.X - point2.X, point1.P);
            BigInteger Y = Math.Mod(lambda * (point1.X - X) - point1.Y, point1.P);

            return new EC_point(point1.A, point1.B, point1.P, X, Y);

        }

        public static EC_point operator *(EC_point point, BigInteger k)
        {

            EC_point result = point;
            k -= 1;
            while (k > 0)
            {
                if (k % 2 != 0)
                {
                    result = result + point;
                    --k;
                }
                else
                {
                    k = k / 2;
                    point = point + point;
                }
            }

            return result;
        }

        public static EC_point operator *(BigInteger k, EC_point point)
        {
            return point * k;
        }

        public static bool operator ==(EC_point point1, EC_point point2)
        {
            if (point1.A != point2.A || point1.B != point2.B || point1.P != point2.P)
                throw new Exception("сравнение точек разных кривых");

            if ((point1.X == point2.X) && (point1.Y == point2.Y))
                return true;

            return false;
        }

        public static bool operator !=(EC_point point1, EC_point point2)
        {
            if (point1.A != point2.A || point1.B != point2.B || point1.P != point2.P)
                throw new Exception("сравнение точек разных кривых");

            if ((point1.X != point2.X) || (point1.Y != point2.Y))
                return true;

            return false;
        }

    }

    class Signature
    {
        EC_point point;
        BigInteger q;
        int hash_length;

        public Signature(EC_point point, BigInteger q, int hash_length)
        {
            this.point = point;
            this.q = q;
            this.hash_length = hash_length;
        }

        //генерация рандомного числа
        BigInteger Random_BigInt(int Length)
        {
            RNGCryptoServiceProvider rng = new RNGCryptoServiceProvider();  // экземпляр крипотостойкого генератора чисел 
            byte[] rnd = new byte[Length];
            rng.GetBytes(rnd);
            BigInteger res = new BigInteger(rnd);
            return BigInteger.Abs(res);  //возвращаем модуль числа
        }

        public BigInteger Generate_Private_Key(int length)
        {
            BigInteger d = new BigInteger();

            do
            {
                d = Random_BigInt(length);
            }
            while (d > 0 && d < q);

            return d;
        }

        public EC_point Generate_Public_Key(BigInteger d)
        {
            return point * d;
        }

        public byte[] Generate_Signature(byte[] hash, BigInteger d)
        {
            BigInteger alpha = new BigInteger(hash);
            BigInteger e = Math.Mod(alpha, q) == 0 ? 1 : Math.Mod(alpha, q);

            BigInteger k;
            BigInteger r;
            BigInteger s;
            do
            {
                do
                {
                    do
                    {
                        k = Random_BigInt(hash_length / 8);
                    }
                    while (k < 1 && k > q - 1);

                    EC_point c = point * k;
                    r = Math.Mod(c.X, q);
                }
                while (r == 0);

                s = Math.Mod(r * d + k * e, q);
            }
            while (s == 0);

            byte[] signature = new byte[hash_length / 4];

            Array.Copy(r.ToByteArray(), 0, signature, 0, r.ToByteArray().Length);
            Array.Copy(s.ToByteArray(), 0, signature, hash_length / 8, s.ToByteArray().Length);

            return signature;
        }


        public bool Verify_Signature(byte[] hash, byte[] signature, EC_point Q)
        {
            byte[] byte_r = new byte[hash_length / 8];
            byte[] byte_s = new byte[hash_length / 8];

            Array.Copy(signature, 0, byte_r, 0, hash_length / 8);
            Array.Copy(signature, hash_length / 8, byte_s, 0, hash_length / 8);

            BigInteger r = new BigInteger(byte_r);
            BigInteger s = new BigInteger(byte_s);

            if (r < 1 || r > q - 1 || s < 1 || s > q - 1)
                return false;

            BigInteger alpha = new BigInteger(hash);
            BigInteger e = Math.Mod(alpha, q) == 0 ? 1 : Math.Mod(alpha, q);
            BigInteger v = Math.Ext_Euclidian(e, q);
            BigInteger z1 = Math.Mod(s * v, q);
            BigInteger z2 = Math.Mod(-(r * v), q);

            EC_point c = z1 * point + z2 * Q;

            BigInteger R = Math.Mod(c.X, q);

            if (R == r)
                return true;

            return false;

        }
    }

    internal class Program
    {
        public static string ByteArrayToString(byte[] byteArray)
        {
            string result = "";
            for (int i = 0; i < byteArray.Length; i++)
            {
                result += Convert.ToString(byteArray[i], 2).PadLeft(8, '0');
            }
            return (result);
        }

        static void Main(string[] args)
        {
            byte[] inputBytes;
            bool outputSize, inputType;

            Console.Write("Enter text: ");
            string message = Console.ReadLine();
            inputBytes = Encoding.Default.GetBytes(message);
            Console.Write("Type input (1 - text, 2 - HexCode): ");
            inputType = (Console.ReadLine() == "1") ? true : false;
            Console.Write("Output size (1 - 256 bits, 2 - 512 bits): ");
            outputSize = (Console.ReadLine() == "1") ? true : false;

            Console.WriteLine("\n");
            byte[] output = Streebog.HashFunc(inputBytes, outputSize, inputType);
            string hexCodes = BitConverter.ToString(output);
            Console.WriteLine($"HexCodes: {hexCodes}");
            BigInteger q = BigInteger.Parse("57896044618658097711785492504343953927082934583725450622380973592137631069619");
            BigInteger p = BigInteger.Parse("57896044618658097711785492504343953926634992332820282019728792003956564821041");
            BigInteger x = BigInteger.Parse("2");
            BigInteger y = BigInteger.Parse("4018974056539037503335449422937059775635739389905545080690979365213431566280");
            BigInteger a = BigInteger.Parse("7");
            BigInteger b = BigInteger.Parse("43308876546767276905765904595650931995942111794451039583252968842033849580414");

            EC_point myPoint = new EC_point(a, b, p, x, y);

            Signature signature = new Signature(myPoint, q, outputSize == true ? 256 : 512);
            BigInteger d = signature.Generate_Private_Key(256);
            EC_point Q = signature.Generate_Public_Key(d);

            byte[] signatureBytes = signature.Generate_Signature(output, d);

            Console.WriteLine($"Эцп сообщния: {BitConverter.ToString(signatureBytes)}");

            if (signature.Verify_Signature(output, signatureBytes, Q) == true)
                Console.WriteLine("ЭЦП верна");
            else Console.WriteLine("Эцп не верна");
        }
    }
}