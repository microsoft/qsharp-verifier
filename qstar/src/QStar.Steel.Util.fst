module QStar.Steel.Util
open Steel.ST.Util
#push-options "--ide_id_info_off"

[@@warn_on_use "uses an axiom"]
noextract
val admit__ (#a:Type)
            (#p:pre_t)
            (#q:a -> vprop)
            (_:unit)
  : STF a p q True (fun _ -> False)

