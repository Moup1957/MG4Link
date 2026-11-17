private fun updateDispoBornes(showDialog: Boolean, onDone: (() -> Unit)?) {
        if (dispoLoading) {
            log("Actualisation de la disponibilité déjà en cours...")
            return
        }
        dispoLoading = true
        status("Dispo bornes : mise à jour...")
        log("Récupération de la disponibilité IRVE dynamique (France)...")
        thread(name = "dispo-irve") {
            try {
                // Recherche dynamique via l'API data.gouv.fr pour éviter les pannes de liens directs
                val apiUrl = "https://www.data.gouv.fr/api/1/datasets/base-nationale-des-irve-data-gouv-infrastructures-de-recharge-pour-vehicules-electriques-donnees-dynamiques/"
                var best: String? = null
                try {
                    val json = httpGet(apiUrl, 15000)
                    val urls = Regex("https:[^\"\\\\]+?\\.csv")
                        .findAll(json).map { it.value }.toList()
                    best = urls.firstOrNull { it.contains(" dynamique") || it.contains("latest") || it.endsWith(".csv") }
                } catch (e: Exception) {
                    log("API data.gouv.fr (dynamique) en échec, essai du lien direct...")
                }
                
                // Lien de secours direct si l'API échoue ou ne renvoie rien
                val targetUrl = best ?: "https://diffuseur.developpement-durable.gouv.fr/adhoc/IRVE/dynamique/latest.csv"

                val newByPdc = HashMap<String, DispoStatus>()
                val newByStation = HashMap<String, MutableList<DispoStatus>>()
                val newGeo = ArrayList<DynPdc>()

                var header: List<String>? = null
                var sep = ';'
                var iPdc = -1
                var iStation = -1
                var iEtat = -1
                var iOcc = -1
                var iCoord = -1
                var iLat = -1
                var iLon = -1

                var totalPdc = 0
                var nbLibre = 0
                var nbOccupe = 0
                var nbHs = 0

                downloadCsv(targetUrl) { line ->
                    if (header == null) {
                        sep = if (line.count { it == ';' } >= line.count { it == ',' }) ';' else ','
                        header = splitCsvLine(line, sep).map { it.trim().lowercase(Locale.ROOT) }
                        iPdc = header!!.indexOfFirst { it == "id_pdc_itinerance" || it == "id_pdc" }
                        iStation = header!!.indexOfFirst { it == "id_station_itinerance" || it == "id_station" }
                        iEtat = header!!.indexOfFirst { it == "etat_pdc" || it == "etat" }
                        iOcc = header!!.indexOfFirst { it == "occupation_pdc" || it == "occupation" || it == "statut_pdc" }
                        iCoord = header!!.indexOf("coordonneesxy")
                        iLat = header!!.indexOfFirst { it == "lat" || it == "latitude" || it == "consolidated_latitude" }
                        iLon = header!!.indexOfFirst { it == "lon" || it == "longitude" || it == "consolidated_longitude" }
                    } else {
                        val f = splitCsvLine(line, sep)
                        val etat = if (iEtat >= 0 && f.size > iEtat) f[iEtat] else ""
                        val occ = if (iOcc >= 0 && f.size > iOcc) f[iOcc] else ""
                        val st = parseIrveDynStatus(etat, occ)
                        val pdcId = if (iPdc >= 0 && f.size > iPdc) f[iPdc].trim() else ""
                        val stId = if (iStation >= 0 && f.size > iStation) f[iStation].trim() else ""

                        var lat = 0.0
                        var lon = 0.0
                        if (iCoord >= 0 && f.size > iCoord) {
                            val ll = parseCoord(f[iCoord])
                            if (ll != null) {
                                lat = ll[0]
                                lon = ll[1]
                            }
                        } else if (iLat >= 0 && iLon >= 0 && f.size > iLat && f.size > iLon) {
                            lat = f[iLat].replace(',', '.').toDoubleOrNull() ?: 0.0
                            lon = f[iLon].replace(',', '.').toDoubleOrNull() ?: 0.0
                        }

                        if (pdcId.isNotEmpty() || stId.isNotEmpty() || (lat != 0.0 && lon != 0.0)) {
                            totalPdc++
                            when (st) {
                                DispoStatus.LIBRE -> nbLibre++
                                DispoStatus.OCCUPE -> nbOccupe++
                                DispoStatus.HORS_SERVICE -> nbHs++
                                DispoStatus.INCONNU -> {}
                            }
                            if (pdcId.isNotEmpty()) {
                                newByPdc[pdcId] = st
                            }
                            if (stId.isNotEmpty()) {
                                newByStation.getOrPut(stId) { ArrayList() }.add(st)
                            }
                            if (lat != 0.0 && lon != 0.0) {
                                newGeo.add(DynPdc(pdcId, stId, lat, lon, st))
                            }
                        }
                    }
                }

                synchronized(dynByPdcId) {
                    dynByPdcId.clear()
                    dynByPdcId.putAll(newByPdc)
                    dynByStationId.clear()
                    dynByStationId.putAll(newByStation)
                    dynGeoList.clear()
                    dynGeoList.addAll(newGeo)
                    dynTotalPdc = totalPdc
                    dynLastUpdateMs = System.currentTimeMillis()
                }

                status("Dispo : $totalPdc PDC")
                log("Disponibilité bornes mise à jour : $totalPdc PDC (Libre : $nbLibre, Occupé : $nbOccupe, HS : $nbHs).")

                if (showDialog) {
                    alert(
                        "Disponibilité bornes",
                        "$totalPdc points de charge mis à jour (France).\n" +
                            "Libre : $nbLibre · Occupé : $nbOccupe · HS : $nbHs\n\n" +
                            "Les bornes sans donnée restent « Inconnu »."
                    )
                }
                if (onDone != null) {
                    handler.post { onDone() }
                }
            } catch (e: Exception) {
                log("Erreur disponibilité bornes : " + e.message)
                status("Dispo : erreur réseau")
                if (showDialog) {
                    alert(
                        "Disponibilité bornes",
                        "Impossible de récupérer la disponibilité en direct : " + e.message +
                            "\n\nLes bornes sans donnée restent « Inconnu »."
                    )
                }
            } finally {
                dispoLoading = false
            }
        }
    }
