import org.bouncycastle.crypto.params.KeyParameter;
import org.bouncycastle.crypto.engines.*;

public class AESEncryptRegularDriver {

    public static byte[] driver(byte[] key, byte [] in, byte [] out) {
        KeyParameter params = new KeyParameter(key);
        org.bouncycastle.crypto.engines.AESEngine cipher = new org.bouncycastle.crypto.engines.AESEngine ();
        cipher.init(true, params);
        cipher.processBlock(in,0,out,0);
        return out; //fixme don't bother to return out (here and elsewhere?)
    }
}
